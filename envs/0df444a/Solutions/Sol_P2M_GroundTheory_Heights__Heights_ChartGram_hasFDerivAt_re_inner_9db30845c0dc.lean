-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartGram_hasFDerivAt_re_inner_9db30845c0dc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:04.590608+00:00
-- url     : https://prove2.me/submissions/da6ba3d1-31a5-466b-8bd5-60fdf1147d05

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped InnerProductSpace
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
namespace GroundTheory.Heights₂.Heights
namespace ChartGram
theorem _root_.solution {u w : E → F} {y : E} {u' w' : E →L[ℝ] F}
    (hu : HasFDerivAt u u' y) (hw : HasFDerivAt w w' y) :
    HasFDerivAt (fun y' => (⟪u y', w y'⟫_ℂ).re)
      (Complex.reCLM.comp ((fderivInnerCLM ℂ (u y, w y)).comp (u'.prod w'))) y :=
  Complex.reCLM.hasFDerivAt.comp y (HasFDerivAt.inner ℂ hu hw)
end ChartGram
end GroundTheory.Heights₂.Heights
