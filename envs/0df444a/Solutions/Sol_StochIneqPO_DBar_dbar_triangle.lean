-- Prove2me | solution 1 for StochIneqPO.DBar.dbar_triangle
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:36:21.43758+00:00
-- url     : https://prove2.me/submissions/3090d2cf-b77f-4781-8970-ace3de156c89

import Mathlib
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_dbar

open MeasureTheory ProbabilityTheory StochIneqPO.DBar

namespace DBarTriAux

lemma measurable_shift' : Measurable (shift (E := ℝ)) :=
  measurable_pi_lambda _ (fun n => measurable_pi_apply _)

def shiftInv (ω : ℤ → ℝ) (n : ℤ) : ℝ := ω (n - 1)

lemma measurable_shiftInv : Measurable shiftInv :=
  measurable_pi_lambda _ (fun n => measurable_pi_apply _)

lemma shiftInv_shift (ω : ℤ → ℝ) : shiftInv (shift ω) = ω := by
  funext n; simp [shiftInv, shift]

lemma map_left_compProd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (η : Kernel α β) [IsSFiniteKernel η] {e : α → α}
    (he : Measurable e) :
    (μ.map e) ⊗ₘ η = (μ ⊗ₘ (η.comap e he)).map (Prod.map e id) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (he.prodMap measurable_id) hs,
    Measure.compProd_apply ((he.prodMap measurable_id) hs),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) he]
  rfl

lemma condKernel_shift_ae (R : Measure (ℤ → ℝ)) [IsProbabilityMeasure R]
    (hR : R.map shift = R)
    (α : Measure ((ℤ → ℝ) × (ℤ → ℝ))) [IsProbabilityMeasure α]
    (hα : α.map (Prod.map shift shift) = α) (hαR : α.fst = R) :
    ((α.condKernel.map shift).comap shiftInv measurable_shiftInv) =ᵐ[R] α.condKernel := by
  set κ := α.condKernel with hκ
  haveI := Kernel.IsMarkovKernel.map κ measurable_shift'
  have hdis : R ⊗ₘ κ = α := by rw [← hαR]; exact α.disintegrate κ
  have key : α = α.fst ⊗ₘ ((κ.map shift).comap shiftInv measurable_shiftInv) := by
    rw [hαR]
    conv_rhs => rw [← hR]
    rw [map_left_compProd R _ measurable_shift']
    have : ((κ.map shift).comap shiftInv measurable_shiftInv).comap shift measurable_shift'
        = κ.map shift := by
      ext1 a; simp only [Kernel.comap_apply, shiftInv_shift]
    rw [this, Measure.compProd_map measurable_shift', hdis,
      Measure.map_map (measurable_shift'.prodMap measurable_id)
        (measurable_id.prodMap measurable_shift')]
    exact hα.symm
  have := eq_condKernel_of_measure_eq_compProd _ key
  rw [hαR] at this
  exact this

lemma integrable_coord_of_map {μ : Measure ((ℤ → ℝ) × (ℤ → ℝ))} {P Q : Measure (ℤ → ℝ)}
    (h1 : μ.map Prod.fst = P) (h2 : μ.map Prod.snd = Q)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q) :
    Integrable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => |z.1 0 - z.2 0|) μ := by
  have h0 : Measurable (fun ω : ℤ → ℝ => ω 0) := measurable_pi_apply 0
  rw [← h1] at hPi; rw [← h2] at hQi
  have a := (integrable_map_measure h0.aestronglyMeasurable measurable_fst.aemeasurable).mp hPi
  have b := (integrable_map_measure h0.aestronglyMeasurable measurable_snd.aemeasurable).mp hQi
  exact (a.sub b).abs

lemma glue (P Q R : Measure (ℤ → ℝ))
    (hR : IsShiftInvariant R)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q)
    (hRi : Integrable (fun ω : ℤ → ℝ => ω 0) R)
    (ν1 ν2 : Measure ((ℤ → ℝ) × (ℤ → ℝ)))
    (hν1 : IsPairShiftInvariant ν1) (h11 : ν1.map Prod.fst = P) (h12 : ν1.map Prod.snd = R)
    (hν2 : IsPairShiftInvariant ν2) (h21 : ν2.map Prod.fst = R) (h22 : ν2.map Prod.snd = Q) :
    ∃ μ : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
      IsPairShiftInvariant μ ∧ μ.map Prod.fst = P ∧ μ.map Prod.snd = Q ∧
      ∫ z, |z.1 0 - z.2 0| ∂μ ≤ ∫ z, |z.1 0 - z.2 0| ∂ν1 + ∫ z, |z.1 0 - z.2 0| ∂ν2 := by
  have hsh := measurable_shift'
  have := hR.1; have := hν1.1; have := hν2.1
  set α := ν1.map Prod.swap with hαdef
  haveI : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  have hαinv : α.map (Prod.map shift shift) = α := by
    rw [hαdef, Measure.map_map (hsh.prodMap hsh) measurable_swap]
    have : (Prod.map (shift (E := ℝ)) (shift (E := ℝ))) ∘ Prod.swap =
        Prod.swap ∘ (Prod.map (shift (E := ℝ)) (shift (E := ℝ))) := by funext z; rfl
    rw [this, ← Measure.map_map measurable_swap (hsh.prodMap hsh), hν1.2]
  have hαR : α.fst = R := by
    show α.map Prod.fst = R
    rw [hαdef, Measure.map_map measurable_fst measurable_swap]; exact h12
  have hβR : ν2.fst = R := h21
  set κ := α.condKernel with hκ
  set lam := ν2.condKernel with hlam
  have hdα : R ⊗ₘ κ = α := by rw [← hαR]; exact α.disintegrate κ
  have hdβ : R ⊗ₘ lam = ν2 := by rw [← hβR]; exact ν2.disintegrate lam
  set γ := R ⊗ₘ (κ ×ₖ lam) with hγ
  haveI := Kernel.IsMarkovKernel.map κ hsh
  haveI := Kernel.IsMarkovKernel.map lam hsh
  -- marginal identities
  have m1 : γ.map (Prod.map id Prod.fst) = α := by
    rw [hγ, ← Measure.compProd_map measurable_fst]
    have : (κ ×ₖ lam).map Prod.fst = κ := by
      rw [← Kernel.fst_eq]; exact Kernel.fst_prod κ lam
    rw [this, hdα]
  have m2 : γ.map (Prod.map id Prod.snd) = ν2 := by
    rw [hγ, ← Measure.compProd_map measurable_snd]
    have : (κ ×ₖ lam).map Prod.snd = lam := by
      rw [← Kernel.snd_eq]; exact Kernel.snd_prod κ lam
    rw [this, hdβ]
  -- invariance of γ
  have hκae := condKernel_shift_ae R hR.2 α hαinv hαR
  have hlamae := condKernel_shift_ae R hR.2 ν2 hν2.2 hβR
  have hinv : γ.map (Prod.map shift (Prod.map shift shift)) = γ := by
    have e1 : (Prod.map shift (Prod.map shift shift) : (ℤ → ℝ) × ((ℤ → ℝ) × (ℤ → ℝ)) → _) =
        Prod.map shift id ∘ Prod.map id (Prod.map shift shift) := rfl
    rw [e1, ← Measure.map_map (hsh.prodMap measurable_id)
      (measurable_id.prodMap (hsh.prodMap hsh)), hγ,
      ← Measure.compProd_map (hsh.prodMap hsh), ← Kernel.map_prod_map _ _ hsh hsh]
    set η := ((κ.map shift ×ₖ lam.map shift).comap shiftInv measurable_shiftInv) with hη
    have hηc : η.comap shift hsh = κ.map shift ×ₖ lam.map shift := by
      ext1 a; simp only [hη, Kernel.comap_apply, shiftInv_shift]
    rw [← hηc, ← map_left_compProd R η hsh, hR.2, hη, Kernel.comap_prod]
    apply Measure.compProd_congr
    filter_upwards [hκae, hlamae] with z hz1 hz2
    rw [Kernel.prod_apply, Kernel.prod_apply, hz1, hz2]
  set μ := γ.map Prod.snd with hμ
  have h0 : Measurable (fun ω : ℤ → ℝ => ω 0) := measurable_pi_apply 0
  refine ⟨μ, ⟨Measure.isProbabilityMeasure_map measurable_snd.aemeasurable, ?_⟩, ?_, ?_, ?_⟩
  · rw [hμ, Measure.map_map (hsh.prodMap hsh) measurable_snd]
    have : (Prod.map (shift (E := ℝ)) (shift (E := ℝ))) ∘
        (Prod.snd : (ℤ → ℝ) × ((ℤ → ℝ) × (ℤ → ℝ)) → _) =
        Prod.snd ∘ Prod.map shift (Prod.map shift shift) := rfl
    rw [this, ← Measure.map_map measurable_snd (hsh.prodMap (hsh.prodMap hsh)), hinv]
  · rw [hμ, Measure.map_map measurable_fst measurable_snd]
    have : (Prod.fst ∘ Prod.snd : (ℤ → ℝ) × ((ℤ → ℝ) × (ℤ → ℝ)) → _) =
        Prod.snd ∘ Prod.map id Prod.fst := rfl
    rw [this, ← Measure.map_map measurable_snd (measurable_id.prodMap measurable_fst), m1,
      hαdef, Measure.map_map measurable_snd measurable_swap]
    exact h11
  · rw [hμ, Measure.map_map measurable_snd measurable_snd]
    have : (Prod.snd ∘ Prod.snd : (ℤ → ℝ) × ((ℤ → ℝ) × (ℤ → ℝ)) → _) =
        Prod.snd ∘ Prod.map id Prod.snd := rfl
    rw [this, ← Measure.map_map measurable_snd (measurable_id.prodMap measurable_snd), m2]
    exact h22
  · -- the cost estimate
    have hc1 : Integrable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => |z.1 0 - z.2 0|) ν1 :=
      integrable_coord_of_map h11 h12 hPi hRi
    have hc2 : Integrable (fun z : (ℤ → ℝ) × (ℤ → ℝ) => |z.1 0 - z.2 0|) ν2 :=
      integrable_coord_of_map h21 h22 hRi hQi
    have hmf1 : Measurable (fun p : (ℤ → ℝ) × (ℤ → ℝ) => |p.2 0 - p.1 0|) := by fun_prop
    have hmf2 : Measurable (fun p : (ℤ → ℝ) × (ℤ → ℝ) => |p.1 0 - p.2 0|) := by fun_prop
    have hcα : Integrable (fun p : (ℤ → ℝ) × (ℤ → ℝ) => |p.2 0 - p.1 0|) α :=
      (integrable_map_measure hmf1.aestronglyMeasurable measurable_swap.aemeasurable).mpr hc1
    have hg1 : Integrable (fun t : (ℤ → ℝ) × ((ℤ → ℝ) × (ℤ → ℝ)) => |t.2.1 0 - t.1 0|) γ := by
      rw [← m1] at hcα
      exact (integrable_map_measure hmf1.aestronglyMeasurable
        (measurable_id.prodMap measurable_fst).aemeasurable).mp hcα
    have hg2 : Integrable (fun t : (ℤ → ℝ) × ((ℤ → ℝ) × (ℤ → ℝ)) => |t.1 0 - t.2.2 0|) γ := by
      rw [← m2] at hc2
      exact (integrable_map_measure hmf2.aestronglyMeasurable
        (measurable_id.prodMap measurable_snd).aemeasurable).mp hc2
    have i1 : ∫ t, |t.2.1 0 - t.1 0| ∂γ = ∫ z, |z.1 0 - z.2 0| ∂ν1 := by
      have := integral_map (μ := γ) (measurable_id.prodMap measurable_fst).aemeasurable
        hmf1.aestronglyMeasurable
      rw [m1] at this
      refine this.symm.trans ?_
      rw [hαdef, integral_map measurable_swap.aemeasurable hmf1.aestronglyMeasurable]
      rfl
    have i2 : ∫ t, |t.1 0 - t.2.2 0| ∂γ = ∫ z, |z.1 0 - z.2 0| ∂ν2 := by
      have := integral_map (μ := γ) (measurable_id.prodMap measurable_snd).aemeasurable
        hmf2.aestronglyMeasurable
      rw [m2] at this
      exact this.symm
    rw [hμ, integral_map measurable_snd.aemeasurable hmf2.aestronglyMeasurable, ← i1, ← i2,
      ← integral_add hg1 hg2]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => abs_nonneg _))
      (hg1.add hg2) (Filter.Eventually.of_forall (fun t => ?_))
    have := abs_sub_le (t.2.1 0) (t.1 0) (t.2.2 0)
    simpa using this

lemma set_nonempty (P Q : Measure (ℤ → ℝ)) (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q) :
    ∃ ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
      IsPairShiftInvariant ν ∧ ν.map Prod.fst = P ∧ ν.map Prod.snd = Q := by
  have := hP.1; have := hQ.1
  have hsh := measurable_shift'
  refine ⟨P.prod Q, ⟨inferInstance, ?_⟩, ?_, ?_⟩
  · rw [← Measure.map_prod_map P Q hsh hsh, hP.2, hQ.2]
  · simp
  · simp

lemma bdd (P Q : Measure (ℤ → ℝ)) :
    BddBelow {c : ℝ | ∃ ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
      IsPairShiftInvariant ν ∧ ν.map Prod.fst = P ∧ ν.map Prod.snd = Q ∧
      c = ∫ z, |z.1 0 - z.2 0| ∂ν} := by
  refine ⟨0, ?_⟩
  rintro c ⟨μ, -, -, -, rfl⟩
  exact integral_nonneg (fun z => abs_nonneg _)

end DBarTriAux

open DBarTriAux in
theorem solution
    (P Q R : Measure (ℤ → ℝ))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q) (hR : IsShiftInvariant R)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q)
    (hRi : Integrable (fun ω : ℤ → ℝ => ω 0) R) :
    dbar P Q ≤ dbar P R + dbar R Q := by
  obtain ⟨ν0, hν0, h01, h02⟩ := set_nonempty P R hP hR
  obtain ⟨ν0', hν0', h01', h02'⟩ := set_nonempty R Q hR hQ
  have key : ∀ c1 ∈ {c : ℝ | ∃ ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
        IsPairShiftInvariant ν ∧ ν.map Prod.fst = P ∧ ν.map Prod.snd = R ∧
        c = ∫ z, |z.1 0 - z.2 0| ∂ν},
      ∀ c2 ∈ {c : ℝ | ∃ ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
        IsPairShiftInvariant ν ∧ ν.map Prod.fst = R ∧ ν.map Prod.snd = Q ∧
        c = ∫ z, |z.1 0 - z.2 0| ∂ν}, dbar P Q ≤ c1 + c2 := by
    rintro c1 ⟨ν1, hν1, h11, h12, rfl⟩ c2 ⟨ν2, hν2, h21, h22, rfl⟩
    obtain ⟨μ, hμ, hμ1, hμ2, hcost⟩ := glue P Q R hR hPi hQi hRi ν1 ν2 hν1 h11 h12 hν2 h21 h22
    exact (csInf_le (bdd P Q) ⟨μ, hμ, hμ1, hμ2, rfl⟩).trans hcost
  have step1 : ∀ c2 ∈ {c : ℝ | ∃ ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
        IsPairShiftInvariant ν ∧ ν.map Prod.fst = R ∧ ν.map Prod.snd = Q ∧
        c = ∫ z, |z.1 0 - z.2 0| ∂ν}, dbar P Q - c2 ≤ dbar P R := by
    intro c2 hc2
    refine le_csInf ⟨_, ν0, hν0, h01, h02, rfl⟩ (fun c1 hc1 => ?_)
    have := key c1 hc1 c2 hc2
    linarith
  have step2 : dbar P Q - dbar P R ≤ dbar R Q := by
    refine le_csInf ⟨_, ν0', hν0', h01', h02', rfl⟩ (fun c2 hc2 => ?_)
    have := step1 c2 hc2
    linarith
  linarith
