-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_conePoints_iff_a6c2c57083d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:19.590677+00:00
-- url     : https://prove2.me/submissions/cd693b14-4711-4920-89fa-16784d0b2ff9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_reindex_reindexInv_8776e617678c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_oneBlockIdeal_iff_d2a1be6e1df4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_evalCone_eq_eval_60eb02e07a84

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
theorem _root_.solution (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (z : Cone (oneBlockSizes e r) ℂ) :
    z ∈ Heights.conePoints (Heights.oneBlockIdeal om) ℂ ↔
      coneToPairs z ∈ mcPts (mCoordIdeal (oneBlockPt om r)) := by
  constructor
  · rintro ⟨hz, hf⟩
    refine ⟨fun _ ↦ ?_, fun g hg ↦ ?_⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp (hz ())
      exact ⟨oneBlockIndex e r i, by simpa [coneToPairs] using hi⟩
    · have hmem : rename (oneBlockReindexInv e r) g ∈ Heights.oneBlockIdeal om := by
        rw [mem_oneBlockIdeal_iff, rename_reindex_reindexInv]
        exact hg
      have h := hf _ hmem
      rwa [evalCone_eq_eval, rename_reindex_reindexInv] at h
  · rintro ⟨hz, hf⟩
    refine ⟨fun _ h ↦ ?_, fun f hf' ↦ ?_⟩
    · obtain ⟨q, hq⟩ := hz ()
      exact hq (by simp [coneToPairs, h])
    · rw [evalCone_eq_eval]
      exact hf _ ((mem_oneBlockIdeal_iff om f).1 hf')
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
