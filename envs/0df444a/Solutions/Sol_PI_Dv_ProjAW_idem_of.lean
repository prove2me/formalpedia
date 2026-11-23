-- Prove2me | solution 1 for PI.Dv.ProjAW.idem_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:21.528805+00:00
-- url     : https://prove2.me/submissions/b31ed1c4-66fb-4c49-822d-bbd379e50efa

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
theorem _root_.solution {f : Module.End K A.V} (hf : f * f = f) {x : A.V} (hx : x ∈ LinearMap.range f) :
    f x = x := by
  obtain ⟨y, rfl⟩ := hx
  have h := LinearMap.congr_fun hf y
  simpa [Module.End.mul_apply] using h
end PI.Dv.ProjAW
