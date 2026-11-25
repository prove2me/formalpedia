-- Prove2me | solution 1 for PI.LevelKSplit.W.NCA.map_eq_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:02.302102+00:00
-- url     : https://prove2.me/submissions/91febd13-8dd6-4841-ae59-ddfd17d11f54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA
open scoped TensorProduct
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
namespace PI.LevelKSplit.W.NCA
theorem _root_.solution (p : V →+ V) (hp : Continuous p) (hpp : ∀ v, p (p v) = p v)
    (W : AddSubgroup V) (hW : ∀ v, v ∈ W ↔ p v = v)
    (g : V →+ V) (hg : Continuous g) (hgU : ∀ u, p u = 0 → g u = u)
    (hV : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map g = μ)
    (f : W → W) (hf : ∀ w, (f w : V) = g w) (μ : Measure W) (hμ : μ.IsAddHaarMeasure) :
    μ.map f = μ := by
  classical
  haveI := hμ
  set U : AddSubgroup V := p.ker with hUdef
  have hWc : IsClosed (W : Set V) := by
    have e : (W : Set V) = {v | p v = v} := Set.ext fun v => hW v
    rw [e]
    exact isClosed_eq hp continuous_id
  have hUc : IsClosed (U : Set V) := by
    have e : (U : Set V) = {v | p v = 0} := Set.ext fun v => by simp [hUdef, AddMonoidHom.mem_ker]
    rw [e]
    exact isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace W := hWc.locallyCompactSpace
  haveI : LocallyCompactSpace U := hUc.locallyCompactSpace
  haveI : BorelSpace W := Subtype.borelSpace (W : Set V)
  haveI : BorelSpace U := Subtype.borelSpace (U : Set V)
  haveI : SecondCountableTopology W := TopologicalSpace.Subtype.secondCountableTopology (W : Set V)
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set V)
  haveI : BorelSpace (W × U) := Prod.borelSpace
  have hpW : ∀ w : W, p w = w := fun w => (hW w).1 w.2
  have hfc : Continuous f := by
    apply continuous_induced_rng.2
    have e : (Subtype.val ∘ f : W → V) = fun w : W => g (w : V) := funext hf
    rw [e]
    exact hg.comp continuous_subtype_val
  let Φ : W × U →+ V := W.subtype.comp (AddMonoidHom.fst W U) + U.subtype.comp (AddMonoidHom.snd W U)
  have hΦ : ∀ x : W × U, Φ x = (x.1 : V) + (x.2 : V) := fun x => rfl
  have hΦc : Continuous Φ := by
    have e : (Φ : W × U → V) = fun x => (x.1 : V) + (x.2 : V) := funext hΦ
    rw [e]
    exact (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
  let Ψ : V → W × U := fun v => (⟨p v, (hW _).2 (hpp v)⟩,
    ⟨v - p v, by simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp]⟩)
  have hΨc : Continuous Ψ :=
    (hp.subtype_mk fun v => (hW _).2 (hpp v)).prodMk ((continuous_id.sub hp).subtype_mk fun v => by
      simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp])
  have hΦΨ : ∀ v, Φ (Ψ v) = v := fun v => by
    rw [hΦ]
    simp [Ψ]
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    rintro ⟨w, u⟩
    have hu : p u = 0 := u.2
    have hpx : p (Φ (w, u)) = w := by rw [hΦ, map_add, hpW, hu, add_zero]
    apply Prod.ext
    · apply Subtype.ext
      show p (Φ (w, u)) = w
      exact hpx
    · apply Subtype.ext
      show Φ (w, u) - p (Φ (w, u)) = u
      rw [hpx, hΦ]
      simp
  have hΦs : Function.Surjective Φ := fun v => ⟨Ψ v, hΦΨ v⟩
  let e : (W × U) ≃ₜ V :=
    { toFun := Φ, invFun := Ψ, left_inv := hΨΦ, right_inv := hΦΨ,
      continuous_toFun := hΦc, continuous_invFun := hΨc }
  let ν : Measure U := Measure.addHaar
  set P : Measure (W × U) := μ.prod ν with hP
  haveI hPH : P.IsAddHaarMeasure := by rw [hP]; infer_instance
  have hHaar : (P.map Φ).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map P Φ hΦc hΦs e.isClosedEmbedding.tendsto_cocompact
  have hmap := hV _ hHaar
  have hgΦ : (g : V → V) ∘ Φ = Φ ∘ Prod.map f id := by
    funext x
    obtain ⟨w, u⟩ := x
    simp only [Function.comp, Prod.map, id, hΦ, map_add, hgU u u.2, hf]
  have hfm : Measurable f := hfc.measurable
  have hPm : Measurable (Prod.map f (id : U → U)) := hfm.prodMap measurable_id
  rw [Measure.map_map hg.measurable hΦc.measurable, hgΦ,
    ← Measure.map_map hΦc.measurable hPm] at hmap
  have hinv : ∀ Q : Measure (W × U), (Q.map Φ).map Ψ = Q := by
    intro Q
    rw [Measure.map_map hΨc.measurable hΦc.measurable]
    have e2 : Ψ ∘ Φ = id := funext hΨΦ
    rw [e2, Measure.map_id]
  have hP' : P.map (Prod.map f id) = P := by
    have h2 := congrArg (fun Q => Q.map Ψ) hmap
    simpa only [hinv] using h2
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (0 : U)
  have hK0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have hKt : ν K ≠ ⊤ := hKc.measure_lt_top.ne
  ext A hA
  rw [Measure.map_apply hfm hA]
  have h1 : (P.map (Prod.map f id)) (A ×ˢ K) = P (A ×ˢ K) := by rw [hP']
  rw [Measure.map_apply hPm (hA.prod hKc.measurableSet)] at h1
  have hpre : Prod.map f id ⁻¹' (A ×ˢ K) = (f ⁻¹' A) ×ˢ K := by
    ext x
    simp
  rw [hpre, hP, Measure.prod_prod, Measure.prod_prod] at h1
  have h2 := congrArg (fun t => t / ν K) h1
  simp only [ENNReal.mul_div_cancel_right hK0 hKt] at h2
  exact h2
end PI.LevelKSplit.W.NCA
