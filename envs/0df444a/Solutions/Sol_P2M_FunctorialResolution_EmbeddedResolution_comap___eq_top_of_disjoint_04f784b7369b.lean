-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_comap___eq_top_of_disjoint_04f784b7369b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:30.551728+00:00
-- url     : https://prove2.me/submissions/e0614b8e-e86e-4333-b235-b88e1bfe880c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_comap_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme} (I : X.IdealSheafData) (U : X.Opens)
    (h : Disjoint (U : Set X) (I.support : Set X)) : I.comap U.ι = ⊤ := by
  have hempty : ((I.comap U.ι).support : Set U) = ∅ := by
    rw [support_comap_eq]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hxU : U.ι.base x ∈ (U : Set X) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact Set.disjoint_left.mp h hxU hx
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  exact SetLike.ext' hempty
end FunctorialResolution.EmbeddedResolution
