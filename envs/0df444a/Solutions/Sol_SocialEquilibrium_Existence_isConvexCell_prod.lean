-- Prove2me | solution 1 for SocialEquilibrium.Existence.isConvexCell_prod
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:27:26.857362+00:00
-- url     : https://prove2.me/submissions/6cbb271b-fcb9-4d74-89f7-bb43eba3c6cd

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron

namespace SocialEquilibrium.Existence

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

theorem solution {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {A : Set E} {B : Set F} (hA : IsConvexCell A) (hB : IsConvexCell B) :
    IsConvexCell (A ×ˢ B) := by
  obtain ⟨s, hs, rfl⟩ := hA
  obtain ⟨t, ht, rfl⟩ := hB
  refine ⟨s ×ˢ t, hs.product ht, ?_⟩
  rw [Finset.coe_product, convexHull_prod]
