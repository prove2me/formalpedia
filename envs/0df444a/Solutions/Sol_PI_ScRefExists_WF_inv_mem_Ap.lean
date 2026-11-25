-- Prove2me | solution 1 for PI.ScRefExists.WF.inv_mem_Ap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:21:26.793294+00:00
-- url     : https://prove2.me/submissions/41510fde-2d0b-44e7-956b-dd5597f4edc0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Theorems.Thm_PI_ScRefExists_WF_mem_Ap
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
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open Matrix
open PI PI.ScRefExists PI.ScRefExists.WF
variable (I : Formalism.MainNotions.S.AutInst)
variable {I}
namespace PI.ScRefExists.WF
theorem _root_.solution {p s : ℕ} (hp : p.Prime) (hs : Nat.Coprime s p) : ((s : I.E))⁻¹ ∈ Ap I p := by
  have hs0 : (s : I.E) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr ?_
    rintro rfl
    rw [Nat.coprime_zero_left] at hs
    exact hp.one_lt.ne' hs
  exact mem_Ap.mpr ⟨s, hs, 1, by rw [mul_inv_cancel₀ hs0]; simp⟩
end PI.ScRefExists.WF
