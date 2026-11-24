-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_old_c1a40a519d86
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:48.642833+00:00
-- url     : https://prove2.me/submissions/caff6073-54c8-405a-a6c0-ecc1427d95bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicNew

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockDimension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
  (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockDimension
theorem _root_.solution (v : Coord n) :
    plusMap D (X (D.oldCoord v)) = C (P.mkF (X v)) * X (some v.1) := by
  simp [plusMap, AddBlockData.extMap, AddBlockData.oldCoord, AddBlockData.extVal]
end GroundTheory.Heights₂.Heights.AddBlockDimension
