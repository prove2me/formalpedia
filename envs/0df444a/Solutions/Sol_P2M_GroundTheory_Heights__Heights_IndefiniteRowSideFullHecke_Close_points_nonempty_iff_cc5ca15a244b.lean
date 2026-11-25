-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_points_nonempty_iff_cc5ca15a244b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:41.007491+00:00
-- url     : https://prove2.me/submissions/dc2bfa5d-9cf9-44f7-ad65-aa787131d833

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous

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
theorem _root_.solution (hB : IndefiniteRowSideFullHecke.Close.SupNormEquality.Statement) (P : ArithVariety n) (k₀ : ι) :
    (P.points ℂ).Nonempty ↔ (oneBlockPoints P k₀).Nonempty := by
  have h := (hB ι n P k₀).2 0 1 (isHomogeneous_one _ _)
  simp only [eval₂_one, norm_one, pow_zero, div_one] at h
  rcases (P.points ℂ).eq_empty_or_nonempty with h1 | h1 <;>
    rcases (oneBlockPoints P k₀).eq_empty_or_nonempty with h2 | h2
  · simp [h1, h2]
  · rw [h1, h2.image_const, Set.image_empty, Real.sSup_empty, csSup_singleton] at h
    norm_num at h
  · rw [h2, h1.image_const, Set.image_empty, Real.sSup_empty, csSup_singleton] at h
    norm_num at h
  · exact iff_of_true h1 h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
