-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianExtension_proj_incl_940321fee341
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:14.273659+00:00
-- url     : https://prove2.me/submissions/05210596-e4af-497f-95d8-c5fc484b6581

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
namespace GroundTheory.Heights₂.Heights.HermitianExtension
theorem _root_.solution (y : E'.carrier) : X.proj (X.incl y) = 0 := X.exact.apply_apply_eq_zero y
end GroundTheory.Heights₂.Heights.HermitianExtension
