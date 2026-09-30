-- Prove2me | solution 1 for SP4Mission.punctured_homotopy_sphere_contractible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-09T01:55:50.549455+00:00
-- url     : https://prove2.me/submissions/c0ce3379-15bd-4346-b150-206d371f22d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Theorems.Thm_SP4Mission_contractible_of_weaklyContractible_manifold
import Theorems.Thm_SP4Mission_punctured_homotopy_sphere_weaklyContractible

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

/-!
"`Σ⁴ − pt` is contractible" (Freedman 1982, p. 371), reduced to

1. `punctured_homotopy_sphere_weaklyContractible`: the punctured homotopy sphere has trivial
   homotopy groups in all degrees (weak contractibility);
2. `contractible_of_weaklyContractible_manifold`: a weakly contractible second-countable
   topological manifold is contractible (Milnor: manifolds have the homotopy type of CW
   complexes; Whitehead's theorem).

What is verified here is that `M ∖ {p}` is a second-countable Hausdorff topological 4-manifold:
the charts of `M` restrict to the open subset `M ∖ {p}`.
-/

theorem solution
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (hM : Nonempty (ContinuousMap.HomotopyEquiv M S4)) (p : M) :
    ContractibleSpace {x : M // x ≠ p} := by
  -- `M` is second countable (compact and locally Euclidean); so is the subspace `M ∖ {p}`.
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 4)) M
  have : SecondCountableTopology {x : M // x ≠ p} :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  -- The topological charts of `M` restrict to the open set `M ∖ {p}`.
  let _cs : ChartedSpace (EuclideanSpace ℝ (Fin 4)) {x : M // x ≠ p} :=
    (TopologicalSpace.Opens.instChartedSpace (s := ⟨{p}ᶜ, isOpen_compl_singleton⟩) :
      ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (⟨{p}ᶜ, isOpen_compl_singleton⟩ : TopologicalSpace.Opens M))
  -- Weak contractibility (algebraic topology) plus Milnor–Whitehead give contractibility.
  exact contractible_of_weaklyContractible_manifold 4 {x : M // x ≠ p}
    (punctured_homotopy_sphere_weaklyContractible M hM p)
