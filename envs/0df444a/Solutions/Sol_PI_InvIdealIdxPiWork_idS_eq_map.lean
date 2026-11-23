-- Prove2me | solution 1 for PI.InvIdealIdxPiWork.idS_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:54.491842+00:00
-- url     : https://prove2.me/submissions/51b0d95d-85ee-45c1-a88f-5ad7bb9fda5c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvIdealIdxPiWork
open NumberField nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
namespace PI.InvIdealIdxPiWork
theorem _root_.solution (I : Ideal (𝓞 E)) :
    idS I = I.toAddSubgroup.map (algebraMap (𝓞 E) E).toAddMonoidHom := by
  ext x
  simp only [idS, Submodule.mem_toAddSubgroup, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal,
    AddSubgroup.mem_map, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
end PI.InvIdealIdxPiWork
