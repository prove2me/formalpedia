-- Prove2me | solution 1 for PI.Dv.ProjAW.idx_eq_len
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:30.097801+00:00
-- url     : https://prove2.me/submissions/b18797db-3670-460b-86b2-fc3d06b66752

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_IdxEqLen
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_ProjAW_lenAt_eq_zero
import Theorems.Thm_PI_Dv_ProjAW_part2
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
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {f : Module.End K A.V} (hf : f * f = f) :
    idxAt w (imgE A f A.L) (cutE A f A.L) = ((lenAt w (imgE A f A.L) (cutE A f A.L)).toNat : ℤ) := by
  unfold idxAt
  rw [lenAt_eq_zero w (part2 A hf)]
  simp
end PI.Dv.ProjAW
