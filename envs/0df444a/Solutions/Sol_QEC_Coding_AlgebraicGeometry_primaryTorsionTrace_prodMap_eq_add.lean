-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.primaryTorsionTrace_prodMap_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:20:30.684598+00:00
-- url     : https://prove2.me/submissions/907fb4b7-3c7d-47df-b6c9-835b1ff37b7b

import Mathlib.LinearAlgebra.Prod
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_ProdTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_primaryTorsionTrace_comp_comm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N]
    (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (depth : ℕ) :
    primaryTorsionTrace p (f.prodMap g) depth =
      primaryTorsionTrace p f depth + primaryTorsionTrace p g depth := by
  let left : M →ₗ[R] M × N := (LinearMap.inl R M N).comp f
  let right : N →ₗ[R] M × N := (LinearMap.inr R M N).comp g
  have hdecomp : f.prodMap g =
      left.comp (LinearMap.fst R M N) +
        right.comp (LinearMap.snd R M N) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> simp [left, right]
  have hleft := primaryTorsionTrace_comp_comm p
    (LinearMap.fst R M N) left depth
  have hright := primaryTorsionTrace_comp_comm p
    (LinearMap.snd R M N) right depth
  have hleftMap : (LinearMap.fst R M N).comp left = f := by
    apply LinearMap.ext
    intro x
    rfl
  have hrightMap : (LinearMap.snd R M N).comp right = g := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hdecomp, primaryTorsionTrace_add]
  exact congrArg₂ (· + ·)
    (hleft.trans (congrArg (fun h ↦ primaryTorsionTrace p h depth) hleftMap))
    (hright.trans (congrArg (fun h ↦ primaryTorsionTrace p h depth) hrightMap))
end QEC.Coding.AlgebraicGeometry
