-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forms_of_block_f0b3b11b368b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:56:03.474518+00:00
-- url     : https://prove2.me/submissions/606818ea-c190-47cc-86ce-a561ad002a38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exists_rename_of_block_6c006f28b61f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_isWeightedHomogeneous_unit_iff_07c0a93ceda5

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
theorem _root_.solution (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    ∃ f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ n k₀)) f' (fun _ ↦ m) ∧
        rename (Heights.blockIncl k₀) f' = f := by
  obtain ⟨g, hg, rfl⟩ := exists_rename_of_block k₀ m f hf
  refine ⟨rename (blockCoordEquiv (n := n) k₀) g, ?_, ?_⟩
  · rw [isWeightedHomogeneous_unit_iff]
    exact hg.rename_isHomogeneous
  · rw [rename_rename]
    rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
