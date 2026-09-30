-- Prove2me | solution 1 for SP4Mission.punctured_almost_smooth_homotopy_sphere_homeomorph_euclidean
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T05:10:30.48516+00:00
-- url     : https://prove2.me/submissions/0bb55a88-1700-4633-94b8-f16a0e24b53e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4Ends
import Theorems.Thm_SP4Mission_smooth_contractible_scAtInfinity_homeomorph_euclidean
import Theorems.Thm_SP4Mission_punctured_homotopy_sphere_contractible
import Theorems.Thm_SP4Mission_compl_singleton_simplyConnectedAtInfinity

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

/-!
The `ω = 0` uniqueness step of Freedman's Theorem 1.5, in its punctured form, reduced along the
proof of Freedman's Corollary 1.2 (1982, p. 366) to

1. `smooth_contractible_scAtInfinity_homeomorph_euclidean`: a smooth contractible 4-manifold
   which is simply connected at infinity is homeomorphic to `ℝ⁴` (the proper h-cobordism
   `W = V_Σ × [0,1) ∪ B⁴ × 1` and Theorem 10.4);
2. `punctured_homotopy_sphere_contractible`: `M ∖ {p}` is contractible ("Σ⁴ − pt is
   contractible", p. 371);
3. `compl_singleton_simplyConnectedAtInfinity`: the complement of a point in a compact
   4-manifold is simply connected at infinity (its end is a punctured 4-ball).

The smooth structure on `M ∖ {p}` supplied by the hypotheses is exactly the smooth structure
`V_Σ` of Corollary 1.2's proof. What is checked here is that the punctured manifold satisfies the
remaining hypotheses of (1): it is Hausdorff and second countable as a subspace of the compact
locally Euclidean space `M`.
-/

theorem solution
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) (p : M)
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) {x : M // x ≠ p}]
    [IsManifold (𝓡 4) ∞ {x : M // x ≠ p}] :
    Nonempty ({x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 4)) := by
  -- `M` is second countable (compact and locally Euclidean), hence so is `M ∖ {p}`.
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 4)) M
  have : SecondCountableTopology {x : M // x ≠ p} :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  -- `M ∖ {p}` is contractible (algebraic topology of the homotopy sphere).
  have : ContractibleSpace {x : M // x ≠ p} := punctured_homotopy_sphere_contractible M hM p
  -- `M ∖ {p}` is simply connected at infinity (its end is a punctured 4-ball).
  have hsc : SP4Ends.SimplyConnectedAtInfinity {x : M // x ≠ p} :=
    compl_singleton_simplyConnectedAtInfinity 4 (by norm_num) M p
  -- Freedman: a smooth contractible 4-manifold simply connected at infinity is `ℝ⁴`.
  exact smooth_contractible_scAtInfinity_homeomorph_euclidean {x : M // x ≠ p} hsc
