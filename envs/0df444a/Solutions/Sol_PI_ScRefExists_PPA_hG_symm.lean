-- Prove2me | solution 1 for PI.ScRefExists.PPA.hG_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:20:35.168215+00:00
-- url     : https://prove2.me/submissions/dce3b1d1-85ad-4d43-b871-3933079ed8fb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.PPA
theorem _root_.solution (x y : Fin I.n → I.E) : hG I y x = star (hG I x y) := by
  have hJ : ∀ a b, star (I.J b a) = I.J a b := by
    intro a b
    have h : Formalism.UG.cT (starRingEnd I.E) I.J = I.J := I.J_herm
    have h2 := congrFun (congrFun h a) b
    simpa [Formalism.UG.cT, starRingEnd_apply] using h2
  simp only [hG, Formalism.UG.hform, starRingEnd_apply, star_sum, star_mul', star_star]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ a b]
  ring
end PI.ScRefExists.PPA
