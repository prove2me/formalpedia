-- Prove2me | solution 1 for PI.WFJM.loweringPart_rightAction_inl_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:36.259086+00:00
-- url     : https://prove2.me/submissions/7ad3de95-c8e0-4f0f-8def-33ff7f83b181

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_fockAct2_Eab
import Theorems.Thm_PI_WFJM_minusPart_sum
import Theorems.Thm_PI_WFJM_minusPart_omE_pn
import Theorems.Thm_PI_WFJM_minusPart_omE_np

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
variable {p q r s : ℕ}
namespace PI.WFJM
theorem _root_.solution (k : Fin r) (l : Fin s) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s (Eab (Sum.inl k) (Sum.inr l))) P = -(lapD (p := p) (q := q) k l P) := by
  rw [fockAct2_Eab, minusPart_sum]
  have h1 : ∀ i : Fin p, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inl i, Sum.inl k) (Sum.inl i, Sum.inr l)) P = 0 :=
    fun i => minusPart_omE_pn _ _ (by rfl) (by rfl) P
  have h2 : ∀ j : Fin q, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inr j, Sum.inl k) (Sum.inr j, Sum.inr l)) P =
        -(PI.FJM.dd (Sum.inr j, Sum.inl k) (Sum.inr j, Sum.inr l) P) :=
    fun j => minusPart_omE_np _ _ (by rfl) (by rfl) P
  simp only [Fintype.sum_sum_type, h1, h2, Finset.sum_const_zero, zero_add, PI.FJM.lapD,
    LinearMap.sum_apply, Finset.sum_neg_distrib]
end PI.WFJM
