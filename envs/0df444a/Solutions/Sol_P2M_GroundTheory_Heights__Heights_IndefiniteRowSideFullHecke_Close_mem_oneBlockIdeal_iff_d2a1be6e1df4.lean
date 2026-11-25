-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockIdeal_iff_d2a1be6e1df4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:05.296953+00:00
-- url     : https://prove2.me/submissions/88433f44-660f-415d-b73d-c4c7f2f2c8e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_injective_48d5d985adbe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_oneBlockMap_746ad23ec5fe

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
    f ∈ Heights.oneBlockIdeal (r := r) om ↔
      rename (oneBlockReindex e r) f ∈ mCoordIdeal (oneBlockPt om r) := by
  unfold Heights.oneBlockIdeal mCoordIdeal
  rw [RingHom.mem_ker, RingHom.mem_ker, ← (coneAff_injective K r).eq_iff, map_zero]
  rw [coneAff_oneBlockMap]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
