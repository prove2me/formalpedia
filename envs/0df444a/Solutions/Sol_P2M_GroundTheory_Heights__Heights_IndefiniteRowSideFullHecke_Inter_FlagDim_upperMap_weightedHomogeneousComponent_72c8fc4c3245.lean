-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_upperMap_weightedHomogeneousComponent_72c8fc4c3245
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:50.98432+00:00
-- url     : https://prove2.me/submissions/210e19ec-fd63-40d8-82e8-7fdb6fee5b10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_rowDeg_injective_e88587175a7a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_upperMap_isWeightedHomogeneous_fe98a9b2e734

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
theorem _root_.solution (f : MRingOver F (PluckerBlocks n n)) (a : Fin (n - 1) → ℕ) :
    weightedHomogeneousComponent (rowWeight n) (rowDeg n a) (upperMap F n f) =
      upperMap F n (weightedHomogeneousComponent (plWeight n) a f) := by
  classical
  conv_lhs => rw [← sum_weightedHomogeneousComponent (plWeight n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  rw [map_sum, map_sum]
  by_cases ha : weightedHomogeneousComponent (plWeight n) a f = 0
  · rw [ha, map_zero]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hab : b = a
    · subst hab
      rw [ha, map_zero, map_zero]
    · exact (upperMap_isWeightedHomogeneous F n _ b
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne _
          (fun h => hab (rowDeg_injective n h).symm)
  · rw [Finset.sum_eq_single a]
    · exact (upperMap_isWeightedHomogeneous F n _ a
        (weightedHomogeneousComponent_isWeightedHomogeneous a f)).weightedHomogeneousComponent_same
    · intro b _ hb
      exact (upperMap_isWeightedHomogeneous F n _ b
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne _
          (fun hab => hb (rowDeg_injective n hab).symm)
    · intro h
      exact absurd ((Set.Finite.mem_toFinset _).2 ha) h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
