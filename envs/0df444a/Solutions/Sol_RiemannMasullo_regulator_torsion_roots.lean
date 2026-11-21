-- Prove2me | solution 1 for RiemannMasullo.regulator_torsion_roots
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:13:16.267878+00:00
-- url     : https://prove2.me/submissions/a8f1a7e2-00df-4db7-bfeb-e3d1034ee1fd

-- Mathlib proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L150-L151
import Mathlib
set_option maxSynthPendingDepth 8
open scoped Classical
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
local notation "𝓤" => Additive ((𝓞 F)ˣ ⧸ Units.torsion F)

theorem solution : Units.torsion F = rootsOfUnity (Units.torsionOrder F) (𝓞 F) := by
  exact (Units.rootsOfUnity_eq_torsion F).symm
