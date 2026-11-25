-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_upperMap_isWeightedHomogeneous_fe98a9b2e734
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:06.596074+00:00
-- url     : https://prove2.me/submissions/65bf3070-4823-4ff2-836d-f3564ac6d54c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_toUpper_flagMinorMap_X_200458d87616
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_rowDeg_single_8a1bfcf146ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_flagMinor_uMat_isWeightedHomogeneous_239a24ec8634
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_pow
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
theorem _root_.solution (f : MRingOver F (PluckerBlocks n n)) (a : Fin (n - 1) → ℕ)
    (hf : IsWeightedHomogeneous (plWeight n) f a) :
    IsWeightedHomogeneous (rowWeight n) (upperMap F n f) (rowDeg n a) := by
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have ha : a = Finsupp.weight (plWeight n) m := (hf (mem_support_iff.1 hm)).symm
  have hC : ∀ c : F, upperMap F n (C c) = C c := by
    intro c
    rw [← MvPolynomial.algebraMap_eq]
    exact (upperMap F n).commutes c
  rw [monomial_eq, map_mul, hC, map_finsuppProd]
  apply IsWeightedHomogeneous.C_mul
  rw [ha, Finsupp.weight_apply, Finsupp.sum, map_sum]
  apply IsWeightedHomogeneous.prod
  intro p _
  show IsWeightedHomogeneous (rowWeight n) (upperMap F n (X p ^ m p)) (rowDeg n (m p • plWeight n p))
  rw [map_pow, map_nsmul]
  apply IsWeightedHomogeneous.pow
  rw [toUpper_flagMinorMap_X, plWeight, rowDeg_single]
  exact flagMinor_uMat_isWeightedHomogeneous F n _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
