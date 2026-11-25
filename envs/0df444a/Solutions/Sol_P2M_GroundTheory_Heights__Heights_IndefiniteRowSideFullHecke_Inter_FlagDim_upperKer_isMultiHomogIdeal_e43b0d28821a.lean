-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_upperKer_isMultiHomogIdeal_e43b0d28821a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:22:43.18662+00:00
-- url     : https://prove2.me/submissions/93b68e07-029e-413a-a927-0aafa0bb9f1b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_upperMap_weightedHomogeneousComponent_72c8fc4c3245
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_isMultiHomog_of_isWeightedHomogeneous_22d326baa3f1

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
theorem _root_.solution : IsMultiHomogIdeal (upperKer F n) := by
  classical
  refine ⟨{f | f ∈ upperKer F n ∧ ∃ a, IsWeightedHomogeneous (plWeight n) f a}, ?_, ?_⟩
  · rintro f ⟨_, a, ha⟩
    exact ⟨a, isMultiHomog_of_isWeightedHomogeneous F n f a ha⟩
  · apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (plWeight n) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      refine Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨?_, a,
        weightedHomogeneousComponent_isWeightedHomogeneous a f⟩
      rw [RingHom.mem_ker, ← upperMap_weightedHomogeneousComponent]
      rw [RingHom.mem_ker] at hf
      rw [hf, map_zero]
    · exact Ideal.span_le.2 fun f hf => hf.1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
