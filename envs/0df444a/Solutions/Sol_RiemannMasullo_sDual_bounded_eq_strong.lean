-- Prove2me | solution 1 for RiemannMasullo.sDual_bounded_eq_strong
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:37:04.84708+00:00
-- url     : https://prove2.me/submissions/8fb90416-aae0-4d62-b79e-b88e4c71e1a0

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean#L136-L138
import Definitions.Def_RiemannMasullo_AppC_Duality

open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise
open RiemannMasullo
local instance {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ V] : ContinuousSMul ℂ V :=
  (PolynormableSpace.withSeminorms ℂ V).continuousSMul

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E] [T2Space E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [PolynormableSpace ℂ F] [T2Space F]

theorem solution :
    (inferInstance : TopologicalSpace (SDual E {T | IsVonNBounded ℂ T})) =
      (inferInstance : TopologicalSpace (StrongDual ℂ E)) := rfl
