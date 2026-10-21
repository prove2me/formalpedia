-- Prove2me | solution 1 for PrivLearn.Parity.claim_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:19:03.62674+00:00
-- url     : https://prove2.me/submissions/27ce13ff-a04a-4f58-b371-3ec04784de93

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace PLP

lemma prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ ν : Measure α}
    {μ' ν' : Measure β} [SFinite μ'] [SFinite ν'] (c c' : ENNReal)
    (h : μ ≤ c • ν) (h' : μ' ≤ c' • ν') : μ.prod μ' ≤ (c * c') • ν.prod ν' := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.prod_apply hs, Measure.smul_apply, Measure.prod_apply hs, smul_eq_mul]
  have hm : Measurable (fun x => ν' (Prod.mk x ⁻¹' s)) := measurable_measure_prodMk_left hs
  calc ∫⁻ x, μ' (Prod.mk x ⁻¹' s) ∂μ ≤ ∫⁻ x, c' * ν' (Prod.mk x ⁻¹' s) ∂μ := by
        apply lintegral_mono
        intro x
        have := Measure.le_iff'.mp h' (Prod.mk x ⁻¹' s)
        simpa using this
    _ = c' * ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ := lintegral_const_mul _ hm
    _ ≤ c' * ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂(c • ν) := by
        gcongr
    _ = (c * c') * ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂ν := by
        rw [lintegral_smul_measure]; ring

lemma pi_le : ∀ (k : ℕ) {O : Fin k → Type*} [∀ i, MeasurableSpace (O i)] (μ ν : ∀ i, Measure (O i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] (c : Fin k → ENNReal),
    (∀ i, μ i ≤ c i • ν i) → Measure.pi μ ≤ (∏ i, c i) • Measure.pi ν := by
  intro k
  induction k with
  | zero =>
    intro O _ μ ν _ _ c h
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | succ k ih =>
    intro O _ μ ν _ _ c h
    rw [Measure.le_iff]
    intro E hE
    let e := MeasurableEquiv.piFinSuccAbove O 0
    have hμ := measurePreserving_piFinSuccAbove μ 0
    have hν := measurePreserving_piFinSuccAbove ν 0
    have hE' : MeasurableSet (e.symm ⁻¹' E) := e.symm.measurable hE
    have hEE : E = e ⁻¹' (e.symm ⁻¹' E) := by
      ext x
      show x ∈ E ↔ e.symm (e x) ∈ E
      rw [e.symm_apply_apply]
    have h1 : Measure.pi μ E = ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) (e.symm ⁻¹' E) := by
      conv_lhs => rw [hEE]
      exact hμ.measure_preimage_equiv _
    have h2 : Measure.pi ν E = ((ν 0).prod (Measure.pi fun j => ν (Fin.succAbove 0 j))) (e.symm ⁻¹' E) := by
      conv_lhs => rw [hEE]
      exact hν.measure_preimage_equiv _
    have h3 := prod_le (c 0) (∏ j : Fin k, c (Fin.succAbove 0 j)) (h 0)
      (ih (fun j => μ (Fin.succAbove 0 j)) (fun j => ν (Fin.succAbove 0 j))
        (fun j => c (Fin.succAbove 0 j)) (fun j => h _))
    rw [Measure.le_iff] at h3
    have h4 := h3 _ hE'
    rw [h1, Measure.smul_apply, h2, smul_eq_mul, Fin.prod_univ_succAbove _ 0]
    rw [Measure.smul_apply, smul_eq_mul] at h4
    exact h4

end PLP

theorem solution {D : Type*} {n k : ℕ} {O : Fin k → Type*} [∀ i, MeasurableSpace (O i)]
    {O' : Type*} [MeasurableSpace O'] (A : ∀ i, (Fin n → D) → Measure (O i))
    [∀ i z, IsProbabilityMeasure (A i z)] (ε : Fin k → ℝ) (hA : ∀ i, PrivLearn.Generic.IsDP (A i) (ε i))
    (g : Kernel (∀ i, O i) O') [IsMarkovKernel g] :
    PrivLearn.Generic.IsDP (fun z => (Measure.pi fun i => A i z).bind g) (∑ i, ε i) := by
  intro z z' hz S hS
  have hle : Measure.pi (fun i => A i z) ≤ (∏ i, ENNReal.ofReal (Real.exp (ε i))) • Measure.pi (fun i => A i z') := by
    apply PLP.pi_le
    intro i
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul]
    exact hA i z z' hz s hs
  have hprod : (∏ i, ENNReal.ofReal (Real.exp (ε i))) = ENNReal.ofReal (Real.exp (∑ i, ε i)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), Real.exp_sum]
  rw [hprod] at hle
  simp only
  rw [Measure.bind_apply hS g.measurable.aemeasurable, Measure.bind_apply hS g.measurable.aemeasurable]
  calc ∫⁻ x, g x S ∂(Measure.pi fun i => A i z)
      ≤ ∫⁻ x, g x S ∂(ENNReal.ofReal (Real.exp (∑ i, ε i)) • Measure.pi fun i => A i z') :=
        lintegral_mono' hle le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]
