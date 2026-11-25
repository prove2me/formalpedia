-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_divCycle_map_apply_89989eae05a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:19:03.768879+00:00
-- url     : https://prove2.me/submissions/7b43b3dc-2c9f-4cff-a072-7beaf65e1425

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_sup_span_map_0a62834bb450
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_mem_divSupp_map_iff_ded792b38804
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_multAt_map_1cf6a0a0a11f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_divCycle_apply_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_divCycle_apply_of_not_mem


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.Relabel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  (e : K ≃ K') (h : ∀ k, ι k ≃ ι' (e k))
namespace GroundTheory.Heights₂.Heights.Targets.Relabel
theorem _root_.solution (V W : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    divCycle (V.map (ringEquiv F e h)) (ringEquiv F e h f) (W.map (ringEquiv F e h)) =
      divCycle V f W := by
  by_cases hs : W ∈ divSupp V f
  · rw [DivisorCycleSwap.divCycle_apply_of_mem hs,
      DivisorCycleSwap.divCycle_apply_of_mem ((mem_divSupp_map_iff e h V W f).2 hs), sup_span_map, multAt_map]
  · rw [DivisorCycleSwap.divCycle_apply_of_not_mem hs,
      DivisorCycleSwap.divCycle_apply_of_not_mem (mt (mem_divSupp_map_iff e h V W f).1 hs)]
end GroundTheory.Heights₂.Heights.Targets.Relabel
