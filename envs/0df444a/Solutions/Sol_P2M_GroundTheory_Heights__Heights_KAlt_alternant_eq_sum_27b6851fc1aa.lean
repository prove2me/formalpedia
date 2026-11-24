-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_alternant_eq_sum_27b6851fc1aa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:40.073993+00:00
-- url     : https://prove2.me/submissions/386d8836-5a6d-4883-b845-87d7350be6b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.KAlt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution (e : ι → ℕ) : alternant e = ∑ π, sgnP π * permTerm e π := by
  simp [alternant, Matrix.det_apply', permTerm, sgnP]
end GroundTheory.Heights₂.Heights.KAlt
