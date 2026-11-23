-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_sc_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:14.399567+00:00
-- url     : https://prove2.me/submissions/15430e40-56ce-4ee5-ae18-2a7050231b0b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution (x : Fv F v) : sc (E := E) v x = algebraMap (Fv F v) (Fv F v ⊗[F] E) x := rfl
end PI.LocFramePrimWork
