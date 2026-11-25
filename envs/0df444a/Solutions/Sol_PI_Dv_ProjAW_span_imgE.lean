-- Prove2me | solution 1 for PI.Dv.ProjAW.span_imgE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:48.106399+00:00
-- url     : https://prove2.me/submissions/88f901f4-96a3-4182-93d5-57c788d18af3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
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
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution (hG : A.Good) (f : Module.End K A.V) :
    Submodule.span K (imgE A f A.L : Set A.V) = LinearMap.range f := by
  have h : (imgE A f A.L : Set A.V) = f '' (A.L : Set A.V) := by
    simp only [imgE, Submodule.map_coe, LinearMap.coe_restrictScalars]
  rw [h, Submodule.span_image, hG.2.2, Submodule.map_top]
end PI.Dv.ProjAW
