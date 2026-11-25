-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_liftOld_79e2f292e4c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:16:05.463299+00:00
-- url     : https://prove2.me/submissions/c795eba6-ccce-46ff-853f-ea4617f1ec06

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomial

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
open GroundTheory.Heights₂.Heights.SectionNorm
namespace GroundTheory.Heights₂.Heights.SectionNorm
theorem _root_.solution {P : ArithVariety n} (D : AddBlockData P) (w : Cone D.extSizes ℂ)
    (f : MvPolynomial (Coord n) ℤ) : evalCone w (D.liftOld f) = evalCone (D.basePart₂ w) f := by
  simp only [evalCone, AddBlockData.liftOld, eval₂_rename]
  rfl
end GroundTheory.Heights₂.Heights.SectionNorm
