-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_oneBlockMap_746ad23ec5fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:43.163522+00:00
-- url     : https://prove2.me/submissions/53d802df-3719-40b8-acfc-13d4d8bad8ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_C_ff3a58d5ff90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_X_4498be14a2db

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
theorem _root_.solution (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (f : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) :
    coneAff K r (oneBlockMap (r := r) om f) =
      mConeMap (oneBlockPt om r) (rename (oneBlockReindex e r) f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [show (C a : MvPolynomial (Coord (oneBlockSizes e r)) ℤ) = (a : MvPolynomial _ ℤ) from
      eq_intCast C a]
    simp only [map_intCast]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul]
    rw [hp]
    congr 1
    simp only [oneBlockMap, coe_eval₂Hom, eval₂_X, map_mul, coneAff_C, coneAff_X, rename_X,
      mConeMap, aeval_X, oneBlockReindex, oneBlockPt]
    ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
