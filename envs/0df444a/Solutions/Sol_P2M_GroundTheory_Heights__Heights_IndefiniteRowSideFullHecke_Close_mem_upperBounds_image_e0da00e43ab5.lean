-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_upperBounds_image_e0da00e43ab5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:07.1718+00:00
-- url     : https://prove2.me/submissions/7eaf0875-f27b-4e7e-8ebc-872df7960e5c

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
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (N : ℕ)
    (f : MvPolynomial (Fin (n k₀ + 1)) ℤ) (B : ℝ) :
    B ∈ upperBounds ((fun w ↦ ‖eval₂ (Int.castRingHom ℂ) w f‖ / l2Norm w ^ N) '' oneBlockPoints P k₀) ↔
      ∀ w ∈ oneBlockPoints P k₀, ‖eval₂ (Int.castRingHom ℂ) w f‖ ≤ B * l2Norm w ^ N := by
  rw [mem_upperBounds, Set.forall_mem_image]
  refine forall₂_congr fun w hw ↦ ?_
  rw [div_le_iff₀ (pow_pos (vectorL2Norm_pos hw.1) N)]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
