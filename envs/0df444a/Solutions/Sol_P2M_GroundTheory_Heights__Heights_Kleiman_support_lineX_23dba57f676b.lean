-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_support_lineX_23dba57f676b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:03:41.944873+00:00
-- url     : https://prove2.me/submissions/31d96b2c-6c33-4ec0-9d2d-2a1d50969e64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable (k : Type u) [Field k]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : support (lineX k) = Finset.univ := by
  ext i
  simp [mem_support, lineX_ne_zero]
end GroundTheory.Heights₂.Heights.Kleiman
