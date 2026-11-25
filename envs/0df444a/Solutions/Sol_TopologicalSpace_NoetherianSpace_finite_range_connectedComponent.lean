-- Prove2me | solution 1 for TopologicalSpace.NoetherianSpace.finite_range_connectedComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:46:48.743825+00:00
-- url     : https://prove2.me/submissions/ebcf5e94-731f-4651-9f42-81414cc409c6

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open TopologicalSpace TopologicalSpace.NoetherianSpace
namespace TopologicalSpace.NoetherianSpace
theorem _root_.solution (Y : Type*) [TopologicalSpace Y] [NoetherianSpace Y] :
    (Set.range fun x : Y => connectedComponent x).Finite := by
  classical
  have hfin : (irreducibleComponents Y).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine Set.Finite.subset (hfin.image fun Z => ⋃ z ∈ Z, connectedComponent z) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, ?_⟩
  have hsub : irreducibleComponent x ⊆ connectedComponent x :=
    (irreducibleComponent_mem_irreducibleComponents x).1.2.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  show (⋃ z ∈ irreducibleComponent x, connectedComponent z) = connectedComponent x
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
    rwa [← connectedComponent_eq (hsub hz)] at hyz
  · intro y hy
    exact Set.mem_biUnion mem_irreducibleComponent hy
end TopologicalSpace.NoetherianSpace
