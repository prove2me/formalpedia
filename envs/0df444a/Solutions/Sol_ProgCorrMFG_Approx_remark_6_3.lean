-- Prove2me | solution 1 for ProgCorrMFG.Approx.remark_6_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T13:10:52.477507+00:00
-- url     : https://prove2.me/submissions/2fabef02-ecff-4974-95e8-986c94cf4bf1

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model
import Definitions.Def_ProgCorrMFG_Approx_NPlayer
import Definitions.Def_ProgCorrMFG_Approx_MFG

namespace ProgCorrMFG.Approx.Rem63

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

theorem gammaN_singleton {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Fintype G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (ρ₂ : Measure (Flow T X)) (ρ₁ : Kernel (Flow T X) (Strat T X G)) (N : ℕ)
    (ψ : Fin N → Strat T X G) : gammaN ρ₂ ρ₁ N {ψ} = ∫⁻ m, ∏ j, ρ₁ m {ψ j} ∂ρ₂ := by
  unfold gammaN
  rw [Measure.sum_apply _ (measurableSet_singleton ψ)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_single ψ]
  · simp
  · intro b hb
    simp [hb]

end ProgCorrMFG.Approx.Rem63

open MeasureTheory ProbabilityTheory unitInterval Filter Topology ProgCorrMFG.Approx
  ProgCorrMFG.Approx.Rem63

theorem solution {T : ℕ} {X G : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Fintype G] [Nonempty G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G]
    (ρ : Measure (Strat T X G × Flow T X)) [IsProbabilityMeasure ρ]
    (α : (t : Fin T) → I → (Fin (t.1 + 2) → Meas X) → (X → G))
    (hα_meas : ∀ t, Measurable (fun p : I × (Fin (t.1 + 2) → Meas X) => α t p.1 p.2))
    (hα : ρ = ((volume : Measure I).prod (ρ.map Prod.snd)).map
      (fun p : I × Flow T X => ((fun t => α t p.1 (histSucc p.2 t)), p.2)))
    (ρ₁ : Kernel (Flow T X) (Strat T X G)) [IsMarkovKernel ρ₁]
    (hρ₁ : ρ = ((ρ.map Prod.snd) ⊗ₘ ρ₁).map Prod.swap)
    (N : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → Fin N → I) (μ : Ω → Flow T X) (hZ : Measurable Z) (hμ : Measurable μ)
    (hlaw : P.map (fun ω => (Z ω, μ ω)) =
      (Measure.pi fun _ : Fin N => (volume : Measure I)).prod (ρ.map Prod.snd)) :
    P.map (fun ω j => (fun t => α t (Z ω j) (histSucc (μ ω) t) : Strat T X G)) =
      gammaN (ρ.map Prod.snd) ρ₁ N := by
  classical
  haveI : IsProbabilityMeasure (ρ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂, ρ.map Prod.snd = ρ₂ := ⟨_, rfl⟩
  haveI : IsProbabilityMeasure ρ₂ := hρ₂ ▸ inferInstance
  rw [hρ₂] at hα hρ₁ hlaw ⊢
  -- the suggestion map
  let p : I × Flow T X → Strat T X G := fun q => fun t => α t q.1 (histSucc q.2 t)
  have hp : Measurable p := by
    apply measurable_pi_lambda
    intro t
    have hh : Measurable (fun m : Flow T X => histSucc m t) :=
      measurable_pi_lambda _ fun s => measurable_pi_apply _
    exact (hα_meas t).comp (measurable_fst.prodMk (hh.comp measurable_snd))
  have hp' : Measurable (fun q : I × Flow T X => (p q, q.2)) := hp.prodMk measurable_snd
  -- Step A: ρ₁(·|m) is the law of p(Z, m), for ρ₂-a.e. m
  let g : Strat T X G → Flow T X → ENNReal := fun φ m =>
    (volume : Measure I) ((fun z => (z, m)) ⁻¹' (p ⁻¹' {φ}))
  have hg : ∀ φ, Measurable (g φ) := fun φ =>
    measurable_measure_prodMk_right (hp (measurableSet_singleton φ))
  have hA : ∀ φ, (fun m => ρ₁ m {φ}) =ᵐ[ρ₂] g φ := by
    intro φ
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (Kernel.measurable_coe ρ₁ (measurableSet_singleton φ)) (hg φ) fun B hB _ => ?_
    have e1 : ρ ({φ} ×ˢ B) = ∫⁻ m in B, ρ₁ m {φ} ∂ρ₂ := by
      conv_lhs => rw [hρ₁]
      rw [Measure.map_apply measurable_swap ((measurableSet_singleton φ).prod hB),
        Set.preimage_swap_prod, Measure.compProd_apply_prod hB (measurableSet_singleton φ)]
    have e2 : ρ ({φ} ×ˢ B) = ∫⁻ m in B, g φ m ∂ρ₂ := by
      conv_lhs => rw [hα]
      rw [Measure.map_apply hp' ((measurableSet_singleton φ).prod hB),
        Measure.prod_apply_symm (hp' ((measurableSet_singleton φ).prod hB)),
        ← lintegral_indicator hB]
      congr 1
      funext m
      by_cases hm : m ∈ B
      · rw [Set.indicator_of_mem hm]
        congr 1
        ext z
        simp [hm]
      · rw [Set.indicator_of_notMem hm]
        have : (fun z => (z, m)) ⁻¹' ((fun q : I × Flow T X => (p q, q.2)) ⁻¹' ({φ} ×ˢ B)) = ∅ := by
          ext z; simp [hm]
        rw [this, measure_empty]
    rw [← e1, ← e2]
  have hA' : ∀ᵐ m ∂ρ₂, ∀ φ, ρ₁ m {φ} = g φ m := ae_all_iff.mpr hA
  -- Step B: compute the atoms of the law of the suggestions
  let F : (Fin N → I) × Flow T X → (Fin N → Strat T X G) := fun q j => p (q.1 j, q.2)
  have hF : Measurable F := measurable_pi_lambda _ fun j =>
    hp.comp (((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd)
  have hZμ : Measurable (fun ω => (Z ω, μ ω)) := hZ.prodMk hμ
  have : (fun ω j => (fun t => α t (Z ω j) (histSucc (μ ω) t) : Strat T X G)) =
      F ∘ (fun ω => (Z ω, μ ω)) := rfl
  rw [this, ← Measure.map_map hF hZμ, hlaw, Measure.ext_iff_singleton]
  intro ψ
  rw [Measure.map_apply hF (measurableSet_singleton ψ),
    Measure.prod_apply_symm (hF (measurableSet_singleton ψ)), gammaN_singleton]
  apply lintegral_congr_ae
  filter_upwards [hA'] with m hm
  have hpre : (fun z => (z, m)) ⁻¹' (F ⁻¹' {ψ}) =
      Set.univ.pi (fun j => (fun z => (z, m)) ⁻¹' (p ⁻¹' {ψ j})) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ_pi, F]
    constructor
    · intro h j; rw [← h]
    · intro h; funext j; exact h j
  rw [hpre, Measure.pi_pi]
  congr 1
  funext j
  rw [hm (ψ j)]
