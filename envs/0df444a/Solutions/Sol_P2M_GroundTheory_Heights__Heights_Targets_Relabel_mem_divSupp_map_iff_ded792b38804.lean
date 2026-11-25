-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_mem_divSupp_map_iff_ded792b38804
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:43.216719+00:00
-- url     : https://prove2.me/submissions/efd50f82-719d-4fa0-ac30-121c36094d6b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isRelevant_map_iff_e8200a2a6c10
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_sup_span_map_0a62834bb450
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_ringEquiv_injective_a552ea8108be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_minimalPrimes_map_ringEquiv_b33fb8696bed


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
    W.map (ringEquiv F e h) ∈ divSupp (V.map (ringEquiv F e h)) (ringEquiv F e h f) ↔
      W ∈ divSupp V f := by
  simp only [divSupp, Set.mem_ofPred_eq, sup_span_map, minimalPrimes_map_ringEquiv,
    (map_ringEquiv_injective (ringEquiv F e h)).mem_set_image, isRelevant_map_iff]
end GroundTheory.Heights₂.Heights.Targets.Relabel
