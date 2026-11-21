-- Prove2me | solution 1 for RiemannMasullo.regulator_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:13:15.455313+00:00
-- url     : https://prove2.me/submissions/a302b745-dd3e-4959-832f-d00e5cc1f29d

-- Mathlib proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L145-L146
import Mathlib
set_option maxSynthPendingDepth 8
open scoped Classical
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]
local notation "𝓤" => Additive ((𝓞 F)ˣ ⧸ Units.torsion F)

theorem solution : (Units.logEmbedding F).ker = (Units.torsion F).toAddSubgroup := by
  exact logEmbedding_ker
