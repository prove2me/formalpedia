-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_divSupp_map_iff_5ba5be09b67e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:34:38.634042+00:00
-- url     : https://prove2.me/submissions/2533027c-edc6-47c5-a882-45579428baf0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_iff_08aaf3425488
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_map_iff_44c6feca16d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_sup_span_map_de41977b3b32

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)
include hσ
namespace GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
theorem _root_.solution (V W : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') ∈
        divSupp (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (ren σ f) ↔
      W ∈ divSupp V f := by
  have h1 : W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') ∈
        (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') ⊔
          Ideal.span {ren σ f}).minimalPrimes ↔ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes := by
    rw [← sup_span_map]
    exact map_mem_minimalPrimes_iff _
  exact and_congr h1 (isRelevant_map_iff e σ hσ W)
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
