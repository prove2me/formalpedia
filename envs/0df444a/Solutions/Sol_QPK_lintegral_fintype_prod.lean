-- Prove2me | solution 1 for QPK.lintegral_fintype_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:39.108506+00:00
-- url     : https://prove2.me/submissions/75704b51-7ab6-4a53-886d-3504d9c3a871

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_LintegralFintypeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open QPK
namespace QPK
theorem _root_.solution {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  have hF : Measurable fun x : (i : _) → E i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  by_cases hne : Nonempty ((i : _) → E i)
  · obtain ⟨x0⟩ := hne
    have key : ∀ s : Finset _, ∀ x : (i : _) → E i,
        lmarginal μ s (fun x : (i : _) → E i => ∏ i, f i (x i)) x =
          ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro x
        simp [lmarginal_empty]
      | insert a s ha ih =>
        intro x
        rw [lmarginal_insert _ hF ha]
        simp_rw [ih]
        have hC : ∀ t, ∏ i, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (Function.update x a t i)) =
            f a t * ∏ i ∈ Finset.univ.erase a, (if i ∈ s then ∫⁻ t, f i t ∂(μ i) else f i (x i)) := by
          intro t
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
          congr 1
          · simp [ha]
          · refine Finset.prod_congr rfl fun i hi => ?_
            simp [Function.update_apply, Finset.ne_of_mem_erase hi]
        simp_rw [hC]
        rw [lintegral_mul_const _ (hf a), ← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
        congr 1
        · simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi]
    rw [lintegral_eq_lmarginal_univ x0, key]
    simp
  · have hj : ∃ j, IsEmpty (E j) := by
      by_contra h
      push_neg at h
      exact hne ⟨fun i => (h i).some⟩
    obtain ⟨j, hj⟩ := hj
    haveI : IsEmpty ((i : _) → E i) := not_nonempty_iff.1 hne
    rw [lintegral_of_isEmpty]
    refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
    haveI := hj
    exact lintegral_of_isEmpty _ _
end QPK
