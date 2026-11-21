-- Prove2me | solution 1 for RiemannMasullo.regulator_discrete
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:09:59.215488+00:00
-- url     : https://prove2.me/submissions/2932ef2f-6adc-46f7-864c-73d3fd348645

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L132-L133
import Mathlib
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]

theorem solution : IsDiscrete (Set.range (Units.logEmbedding F)) := by
  have heq : Set.range (Units.logEmbedding F) = (Units.unitLattice F : Set (logSpace F)) := by
    ext x
    exact ⟨fun ⟨u, hu⟩ ↦ ⟨u, trivial, hu⟩, fun ⟨u, _, hu⟩ ↦ ⟨u, hu⟩⟩
  rw [heq]
  exact (inferInstance : DiscreteTopology (Units.unitLattice F)).isDiscrete
