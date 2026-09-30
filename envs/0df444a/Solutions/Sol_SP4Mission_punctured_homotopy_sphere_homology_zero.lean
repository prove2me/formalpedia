-- Prove2me | solution 1 for SP4Mission.punctured_homotopy_sphere_homology_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-09T03:26:59.270406+00:00
-- url     : https://prove2.me/submissions/16ac7068-192e-478b-9f2a-57bac73395fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Definitions.Def_SP4HomologyMap
import Theorems.Thm_SP4Mission_sphere_simplyConnected
import Theorems.Thm_SP4Mission_homotopyEquiv_homology_isIso
import Theorems.Thm_SP4Mission_sphere_homology_zero
import Theorems.Thm_SP4Mission_punctured_closed_manifold_homology

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits

/-!
# Homology of a punctured homotopy four-sphere (proof sketch)

Let `M` be a closed topological `4`-manifold homotopy equivalent to `S⁴`, `p ∈ M`, `V := M ∖ {p}`.
Then `H_k(V; ℤ) = 0` for all `k ≥ 1`.

* `M` is simply connected (it is homotopy equivalent to `S⁴`, and `π₁(S⁴) = 0`).
* `SP4Mission.punctured_closed_manifold_homology`: the inclusion `V → M` induces isomorphisms
  `H_k(V) ≅ H_k(M)` for `k ≠ 4`, and `H_4(V) = 0` (long exact sequence of the pair, excision,
  orientability of the simply connected closed manifold `M`).
* `SP4Mission.homotopyEquiv_homology_isIso`: `H_k(M) ≅ H_k(S⁴)`.
* `SP4Mission.sphere_homology_zero`: `H_k(S⁴) = 0` for `k ≥ 1`, `k ≠ 4`.
-/

/-- The target theorem. -/
theorem solution
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) (p : M) (k : ℕ) (hk : 1 ≤ k) :
    IsZero (SP4Homology.H k {x : M // x ≠ p}) := by
  obtain ⟨e⟩ := id hM
  -- `S⁴` is simply connected, hence so is `M`.
  have : SimplyConnectedSpace S4 := sphere_simplyConnected 5 (by norm_num)
  have : SimplyConnectedSpace M := e.simplyConnectedSpace
  obtain ⟨hiso, hzero⟩ := punctured_closed_manifold_homology 4 M p
  by_cases hk4 : k = 4
  · -- top degree: `H_4(M ∖ {p}) = 0`
    subst hk4
    exact hzero
  · -- other degrees: `H_k(M ∖ {p}) ≅ H_k(M) ≅ H_k(S⁴) = 0`
    have h3 : IsZero (SP4Homology.H k S4) := sphere_homology_zero 4 k hk hk4
    have := hiso k hk4
    have := homotopyEquiv_homology_isIso M S4 e k
    exact h3.of_iso
      ((asIso (SP4Homology.map k (⟨Subtype.val, continuous_subtype_val⟩ : C({x : M // x ≠ p}, M)))).trans
        (asIso (SP4Homology.map k e.toFun)))
