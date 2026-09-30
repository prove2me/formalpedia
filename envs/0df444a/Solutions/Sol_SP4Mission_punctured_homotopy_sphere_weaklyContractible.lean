-- Prove2me | solution 1 for SP4Mission.punctured_homotopy_sphere_weaklyContractible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-09T01:55:49.946759+00:00
-- url     : https://prove2.me/submissions/43307633-f440-492b-b062-a174d9f9e84f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Theorems.Thm_SP4Mission_sphere_simplyConnected
import Theorems.Thm_SP4Mission_compl_singleton_simplyConnected
import Theorems.Thm_SP4Mission_punctured_homotopy_sphere_homology_zero
import Theorems.Thm_SP4Mission_weaklyContractible_of_simplyConnected_of_homology_zero

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits

/-!
Weak contractibility of the punctured homotopy four-sphere, reduced to

1. `compl_singleton_simplyConnected`: removing a point from a simply connected `n`-manifold,
   `n ≥ 3`, leaves it simply connected (van Kampen);
2. `punctured_homotopy_sphere_homology_zero`: `H_k(M ∖ {p}; ℤ) = 0` for `k ≥ 1` (long exact
   sequence of the pair, excision, the fundamental class);
3. `weaklyContractible_of_simplyConnected_of_homology_zero`: a simply connected space with
   vanishing positive-degree integral homology is weakly contractible (Hurewicz).

What is verified here is that `M` itself is simply connected: it is homotopy equivalent to `S⁴`,
and `S⁴ ⊂ ℝ⁵` is simply connected (`sphere_simplyConnected`).
-/

theorem solution
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) (p : M) :
    SP4WeakHomotopy.WeaklyContractible {x : M // x ≠ p} := by
  obtain ⟨h⟩ := id hM
  -- `S⁴` is simply connected, hence so is `M`.
  have : SimplyConnectedSpace S4 := sphere_simplyConnected 5 (by norm_num)
  have : SimplyConnectedSpace M := h.simplyConnectedSpace
  -- `M ∖ {p}` is simply connected (dimension `4 ≥ 3`).
  have : SimplyConnectedSpace {x : M // x ≠ p} :=
    compl_singleton_simplyConnected 4 (by norm_num) M p
  -- Hurewicz: simply connected with vanishing homology is weakly contractible.
  exact weaklyContractible_of_simplyConnected_of_homology_zero {x : M // x ≠ p}
    (fun k hk => punctured_homotopy_sphere_homology_zero M hM p k hk)
