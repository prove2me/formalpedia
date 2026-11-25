-- Prove2me | solution 1 for PI.WFJM.loweringPart_rightAction_inr_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:51:54.409401+00:00
-- url     : https://prove2.me/submissions/8d86dbdf-7332-46e6-9e75-afba21ad9599

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_fockAct2_Eab
import Theorems.Thm_PI_WFJM_minusPart_sum
import Theorems.Thm_PI_WFJM_minusPart_omE_pn
import Theorems.Thm_P2M_PI_WFJM_minusPart_omE_np__e671a62cbaae

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
    minusPart (fockAct2 p q r s (Eab (Sum.inr l) (Sum.inl k))) P = -(lapC (p := p) (q := q) k l P) := by
  rw [fockAct2_Eab, minusPart_sum]
  have h1 : ∀ i : Fin p, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inl i, Sum.inr l) (Sum.inl i, Sum.inl k)) P =
        -(PI.FJM.dd (Sum.inl i, Sum.inl k) (Sum.inl i, Sum.inr l) P) :=
    fun i => minusPart_omE_np' _ _ (by rfl) (by rfl) P
  have h2 : ∀ j : Fin q, FockH1Action.minusPart (FockH1Action.omE (p := p) (q := q) (r := r) (s := s)
      (Sum.inr j, Sum.inr l) (Sum.inr j, Sum.inl k)) P = 0 :=
    fun j => minusPart_omE_pn _ _ (by rfl) (by rfl) P
  simp only [Fintype.sum_sum_type, h1, h2, Finset.sum_const_zero, add_zero, PI.FJM.lapC,
    LinearMap.sum_apply, Finset.sum_neg_distrib]
end PI.WFJM
