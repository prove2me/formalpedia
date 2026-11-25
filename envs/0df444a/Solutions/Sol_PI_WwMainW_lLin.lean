-- Prove2me | solution 1 for PI.WwMainW.lLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:06.253817+00:00
-- url     : https://prove2.me/submissions/b680ef1e-f989-467e-971d-bbd7fd345577

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_LfunEqOfSubset
import Theorems.Thm_PI_WwMainW_Lfun_eq_of_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open PI PI.WwMainW
open PI.WwMain PI.WwMain.KM
namespace PI.WwMainW
theorem _root_.solution : LLin := by
  unfold LLin
  intro Lt l _ N0 N1 Th
  classical
  refine ⟨fun p q => ?_, ?_, fun c p => ?_⟩
  · rw [Lfun_eq_of_subset l N0 N1 Th (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
      Lfun_eq_of_subset l N0 N1 Th p (p.support ∪ q.support) Finset.subset_union_left,
      Lfun_eq_of_subset l N0 N1 Th q (p.support ∪ q.support) Finset.subset_union_right]
    rw [← Finset.sum_add_distrib]
    simp only [MvPolynomial.coeff_add, add_mul]
  · rw [Lfun_eq_of_subset l N0 N1 Th 0 ∅ (by simp)]
    simp
  · have hsub : (MvPolynomial.C c * p).support ⊆ p.support := fun x hx => by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hx
      exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hx)
    rw [Lfun_eq_of_subset l N0 N1 Th (MvPolynomial.C c * p) p.support hsub,
      Lfun_eq_of_subset l N0 N1 Th p p.support subset_rfl, Finset.mul_sum]
    simp only [MvPolynomial.coeff_C_mul, mul_assoc]
end PI.WwMainW
