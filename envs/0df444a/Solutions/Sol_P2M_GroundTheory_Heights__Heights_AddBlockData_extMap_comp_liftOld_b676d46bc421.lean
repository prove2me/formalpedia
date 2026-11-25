-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_comp_liftOld_b676d46bc421
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:34.948008+00:00
-- url     : https://prove2.me/submissions/04bbfeff-4bc4-47c1-bc85-eebca97945d8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtMapLiftOldOfIsWeightedHomogeneous

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockData
theorem _root_.solution :
    D.extMap.comp D.liftOld.toRingHom =
      eval₂Hom (Int.castRingHom _) fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ ?_)
  simp [extMap, liftOld, oldCoord, extVal]
end GroundTheory.Heights₂.Heights.AddBlockData
