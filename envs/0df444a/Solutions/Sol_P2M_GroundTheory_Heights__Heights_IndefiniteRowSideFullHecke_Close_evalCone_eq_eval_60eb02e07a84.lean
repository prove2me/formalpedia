-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_evalCone_eq_eval_60eb02e07a84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:30.620505+00:00
-- url     : https://prove2.me/submissions/8f572cfc-c8f3-45f9-bf68-9871e31a0f16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
variable {K : Type} [Field K] [NumberField K] {e r : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (z : Cone (oneBlockSizes e r) ℂ) (f : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :
    evalCone z f = eval (coneToPairs z) (map (Int.castRingHom ℂ) (rename (oneBlockReindex e r) f)) := by
  rw [eval_map, eval₂_rename, evalCone]
  congr 1
  funext v
  rcases v with ⟨⟨⟩, i⟩
  simp [coneToPairs, oneBlockReindex]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
