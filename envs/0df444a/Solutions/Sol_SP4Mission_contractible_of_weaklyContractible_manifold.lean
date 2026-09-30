-- Prove2me | solution 1 for SP4Mission.contractible_of_weaklyContractible_manifold
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-09T03:49:28.062477+00:00
-- url     : https://prove2.me/submissions/ba9df9a4-0367-4ee4-98fa-c86f71ef95b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Theorems.Thm_SP4Mission_manifold_homotopyEquiv_cwComplex
import Theorems.Thm_SP4Mission_weaklyContractible_of_homotopyEquiv
import Theorems.Thm_SP4Mission_whitehead_contractible

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

/-!
# Milnor–Whitehead: a weakly contractible manifold is contractible (proof sketch)

Let `X` be a Hausdorff, second countable topological `n`-manifold with all homotopy groups trivial.

* `SP4Mission.manifold_homotopyEquiv_cwComplex` (Milnor): `X ≃ Y` for a Hausdorff (countable) CW
  complex `Y`.
* `SP4Mission.weaklyContractible_of_homotopyEquiv`: `Y` is weakly contractible as well.
* `SP4Mission.whitehead_contractible` (Whitehead): the weakly contractible CW complex `Y` is
  contractible.
* Contractibility is invariant under homotopy equivalence
  (`ContinuousMap.HomotopyEquiv.contractibleSpace`), so `X` is contractible.
-/

/-- The target theorem. -/
theorem solution
    (n : ℕ) (X : Type*) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (hX : SP4WeakHomotopy.WeaklyContractible X) :
    ContractibleSpace X := by
  obtain ⟨Y, _, hCW, hT2, _, ⟨e⟩⟩ := manifold_homotopyEquiv_cwComplex n X
  have hY : SP4WeakHomotopy.WeaklyContractible Y := weaklyContractible_of_homotopyEquiv X Y e hX
  have : ContractibleSpace Y := whitehead_contractible Y hY
  exact e.contractibleSpace
