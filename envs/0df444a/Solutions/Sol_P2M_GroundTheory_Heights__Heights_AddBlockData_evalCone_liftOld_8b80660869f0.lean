-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_evalCone_liftOld_8b80660869f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:28.922027+00:00
-- url     : https://prove2.me/submissions/22563f3c-dc9d-4179-a9ac-a34f4718a19a

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
theorem _root_.solution {F : Type*} [CommRing F] (w : Cone D.extSizes F) (f : MvPolynomial (Coord n) ℤ) :
    evalCone w (D.liftOld f) = evalCone (D.basePart₂ w) f := by
  simp only [evalCone, liftOld]
  rw [eval₂_rename]
  rfl
end GroundTheory.Heights₂.Heights.AddBlockData
