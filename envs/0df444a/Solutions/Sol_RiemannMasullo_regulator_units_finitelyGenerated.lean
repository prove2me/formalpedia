-- Prove2me | solution 1 for RiemannMasullo.regulator_units_finitelyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:35:29.60161+00:00
-- url     : https://prove2.me/submissions/44de01dc-ef5b-48dc-881b-87d2e950ac08

-- Mathlib proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L162-L163
import Mathlib
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]

theorem solution : Group.FG (𝓞 F)ˣ := by
  exact Group.fg_iff_monoid_fg.mpr inferInstance
