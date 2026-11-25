-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_chartIdeal_map_9f95b660ddf5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:39.103341+00:00
-- url     : https://prove2.me/submissions/18e0433d-0a6b-4305-b6f4-c154d250a26f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_X_59716f4a930d

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
theorem _root_.solution (V : Ideal (MRingOver F ι)) (i' : ∀ k', ι' k') :
    chartIdeal (V.map (ringEquiv F e h)) i' =
      (chartIdeal V fun k => (h k).symm (i' (e k))).map (ringEquiv F e h) := by
  have hrange : (Set.range fun k' => (X ⟨k', i' k'⟩ : MRingOver F ι') - 1) =
      ringEquiv F e h '' Set.range fun k => (X ⟨k, (h k).symm (i' (e k))⟩ : MRingOver F ι) - 1 := by
    ext x
    simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
    constructor
    · rintro ⟨k', rfl⟩
      obtain ⟨k, rfl⟩ := e.surjective k'
      exact ⟨k, by rw [map_sub, map_one, ringEquiv_X, Equiv.apply_symm_apply]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, by rw [map_sub, map_one, ringEquiv_X, Equiv.apply_symm_apply]⟩
  unfold chartIdeal
  rw [hrange, Ideal.map_sup, Ideal.map_span]
end GroundTheory.Heights₂.Heights.Targets.Relabel
