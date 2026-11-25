-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_upperBounds_points_a57829176757
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:15:22.85581+00:00
-- url     : https://prove2.me/submissions/93e50fd2-b9e8-4c6e-a6a4-afdeb0c1d03c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_pullFS_metric_eq_l2Norm_ff823a80b6e2


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
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (N : ℕ)
    (f : MvPolynomial (Fin (n k₀ + 1)) ℤ) (B : ℝ) :
    B ∈ upperBounds ((fun z : Cone n ℂ ↦
        ‖eval₂ (Int.castRingHom ℂ) (z k₀) f‖ / (pullFS n k₀).metric z ^ N) '' P.points ℂ) ↔
      ∀ z ∈ P.points ℂ, ‖eval₂ (Int.castRingHom ℂ) (z k₀) f‖ ≤ B * l2Norm (z k₀) ^ N := by
  rw [mem_upperBounds, Set.forall_mem_image]
  refine forall₂_congr fun z hz ↦ ?_
  rw [pullFS_metric_eq_l2Norm, div_le_iff₀ (pow_pos (vectorL2Norm_pos (hz.1 k₀)) N)]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
