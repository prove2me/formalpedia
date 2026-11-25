-- Prove2me | solution 1 for PI.ScRefExists.WF.star_mem_Ap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:21:34.77447+00:00
-- url     : https://prove2.me/submissions/bf92299f-065a-4b88-953e-205efb7c4a50

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
theorem _root_.solution {p : ℕ} {x : I.E} (hx : x ∈ Ap I p) : star x ∈ Ap I p := by
  obtain ⟨s, hs, a, ha⟩ := mem_Ap.mp hx
  have hint : IsIntegral ℤ (star (a : I.E)) := by
    have := map_isIntegral_int (starRingEnd I.E) (RingOfIntegers.isIntegral_coe a)
    simpa [starRingEnd_apply] using this
  refine mem_Ap.mpr ⟨s, hs, ⟨star (a : I.E), hint⟩, ?_⟩
  show (s : I.E) * star x = star (a : I.E)
  rw [← ha, star_mul', star_natCast]
end PI.ScRefExists.WF
