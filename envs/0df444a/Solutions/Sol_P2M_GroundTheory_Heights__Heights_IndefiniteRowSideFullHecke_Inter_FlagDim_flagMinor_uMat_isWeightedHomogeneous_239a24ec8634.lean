-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_flagMinor_uMat_isWeightedHomogeneous_239a24ec8634
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:56:20.301721+00:00
-- url     : https://prove2.me/submissions/b4d8a4b7-491d-4a52-bef6-06b616fdfaea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_uMat_isWeightedHomogeneous_64b7e0b33f97
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_sum_single_castLE_817f55e95b1c
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_neg
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution (j : Fin (n - 1)) (S : PluckerBlocks n n j) :
    IsWeightedHomogeneous (rowWeight n) (flagMinor (uMat F n) j S) (rowsUpTo n j) := by
  rw [← sum_single_castLE n j]
  simp only [flagMinor]
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hp : IsWeightedHomogeneous (rowWeight n)
      (∏ i, (uMat F n).submatrix (Fin.castLE (by have := j.2; omega)) (S.1.orderEmbOfFin S.2) (σ i) i)
      (∑ i : Fin (j.val + 1), (Pi.single (Fin.castLE (by have := j.2; omega) i : Fin n) 1 : Fin n → ℕ)) := by
    rw [← Equiv.sum_comp σ]
    apply IsWeightedHomogeneous.prod
    intro i _
    exact uMat_isWeightedHomogeneous F n _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
    exact hp
  · rw [h, Units.neg_smul, one_smul]
    exact hp.neg
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
