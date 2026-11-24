-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_reindex_reindexInv_8776e617678c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:07.221471+00:00
-- url     : https://prove2.me/submissions/92b2e099-bf9b-4116-9ae9-2c6c59514ee2

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
theorem _root_.solution (g : MvPolynomial (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) ℤ) :
    rename (oneBlockReindex e r) (rename (oneBlockReindexInv e r) g) = g := by
  rw [rename_rename]
  convert rename_id_apply g
  funext p
  rcases p with ⟨⟨⟩, q⟩
  simp [oneBlockReindex, oneBlockReindexInv]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
