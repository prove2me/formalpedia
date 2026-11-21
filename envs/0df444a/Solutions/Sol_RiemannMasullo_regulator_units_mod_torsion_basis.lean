-- Prove2me | solution 1 for RiemannMasullo.regulator_units_mod_torsion_basis
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:13:18.483183+00:00
-- url     : https://prove2.me/submissions/c52505cd-0e52-49f9-b406-5c6ef64f01a4

-- Mathlib proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L167-L168
import Mathlib
set_option maxSynthPendingDepth 8
open scoped Classical
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
local notation "𝓤" => Additive ((𝓞 F)ˣ ⧸ Units.torsion F)

theorem solution : Nonempty (Module.Basis (Fin (Units.rank F)) ℤ 𝓤) := by
  exact ⟨Units.basisModTorsion F⟩
