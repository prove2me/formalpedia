-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_intCast_subtype_163f87f566d3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:42.828953+00:00
-- url     : https://prove2.me/submissions/17f5a717-c2fd-4447-a14c-5c8c96e1427c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (A : Subalgebra ℤ Ω) (z : ℤ) :
    (⟨(z : Ω), intCast_mem A z⟩ : A) = (z : A) :=
  Subtype.ext (by simp)
end GroundTheory.Heights₂.Heights.Model
