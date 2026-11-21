-- Prove2me | solution 1 for RiemannMasullo.regulator_closed
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:11:31.843161+00:00
-- url     : https://prove2.me/submissions/196cf9d1-ec7a-4014-898a-0cf1d92b2fc5

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L136-L137
import Mathlib
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]

theorem solution : IsClosed (Set.range (Units.logEmbedding F)) := by
  have heq : Set.range (Units.logEmbedding F) = (Units.unitLattice F : Set (logSpace F)) := by
    ext x
    exact ⟨fun ⟨u, hu⟩ ↦ ⟨u, trivial, hu⟩, fun ⟨u, _, hu⟩ ↦ ⟨u, hu⟩⟩
  rw [heq]
  haveI : DiscreteTopology (Units.unitLattice F).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (Units.unitLattice F))
  exact AddSubgroup.isClosed_of_discrete (H := (Units.unitLattice F).toAddSubgroup)
