-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_sup_span_map_de41977b3b32
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:11.553356+00:00
-- url     : https://prove2.me/submissions/95e7b5cc-e550-41cf-b02c-0d7facc95cea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel

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
omit hσ
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
theorem _root_.solution (V : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    (V ⊔ Ideal.span {f}).map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') =
      V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') ⊔ Ideal.span {ren σ f} := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rfl
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
