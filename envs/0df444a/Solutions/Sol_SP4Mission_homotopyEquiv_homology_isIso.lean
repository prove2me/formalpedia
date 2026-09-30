-- Prove2me | solution 1 for SP4Mission.homotopyEquiv_homology_isIso
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-09T03:18:29.600192+00:00
-- url     : https://prove2.me/submissions/9d5c8e66-05a8-4a84-bc94-c0d095634bc4

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Definitions.Def_SP4HomologyMap

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits AlgebraicTopology

/-!
# A homotopy equivalence induces isomorphisms on singular homology

Hatcher, *Algebraic Topology*, Corollary 2.11. Homotopic maps induce the same map on singular
homology (Mathlib: `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`), so for a
homotopy equivalence `e : X ≃ₕ Y` with homotopy inverse `g` we get
`g_* ∘ e_* = (g ∘ e)_* = id_* = id` and `e_* ∘ g_* = id`; hence `e_*` is an isomorphism.
-/

namespace HIso

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Homotopic maps induce the same map on singular homology. -/
theorem map_eq_of_homotopic (k : ℕ) {f g : C(X, Y)} (h : f.Homotopic g) :
    SP4Homology.map k f = SP4Homology.map k g := by
  obtain ⟨H⟩ := h
  have H' : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := H
  exact H'.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) k

/-- A homotopy equivalence induces isomorphisms on singular homology. -/
theorem isIso_map (k : ℕ) (e : ContinuousMap.HomotopyEquiv X Y) :
    IsIso (SP4Homology.map k e.toFun) := by
  refine ⟨SP4Homology.map k e.invFun, ?_, ?_⟩
  · rw [← SP4Homology.map_comp, map_eq_of_homotopic k e.left_inv, SP4Homology.map_id]
  · rw [← SP4Homology.map_comp, map_eq_of_homotopic k e.right_inv, SP4Homology.map_id]

end HIso

/-- The target theorem. -/
theorem solution
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (k : ℕ) :
    IsIso (SP4Homology.map k e.toFun) :=
  HIso.isIso_map k e
