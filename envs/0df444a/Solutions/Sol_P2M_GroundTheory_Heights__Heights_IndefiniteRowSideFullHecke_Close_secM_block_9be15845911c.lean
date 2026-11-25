-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_secM_block_9be15845911c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:31:40.86227+00:00
-- url     : https://prove2.me/submissions/8966f343-6864-4fcc-a4f3-2ea3c0f846b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isMultiHomog_iff_56fd6da73725
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exists_rename_of_block_6c006f28b61f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_block_isWeightedHomogeneous_56f0bbcc7032

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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (N : ℕ) :
    secM (genPt P) (N • Pi.single k₀ 1) =
      (sec ℤ (fun i : Fin (n k₀ + 1) ↦ genPt P ⟨k₀, i⟩) N).toAddSubgroup := by
  unfold secM
  congr 1
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨g, hg, rfl⟩
    rw [isMultiHomog_iff] at hg
    obtain ⟨h, hh, rfl⟩ := exists_rename_of_block k₀ N g hg
    refine Submodule.mem_map.mpr ⟨h, (mem_homogeneousSubmodule N h).mpr hh, ?_⟩
    change aeval _ h = _
    rw [aeval_rename]
    rfl
  · intro x hx
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.subset_span ⟨rename (fun i ↦ (⟨k₀, i⟩ : Coord n)) h, ?_, ?_⟩
    · rw [isMultiHomog_iff]
      exact rename_block_isWeightedHomogeneous k₀ ((mem_homogeneousSubmodule N h).mp hh)
    · rw [aeval_rename]
      rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
