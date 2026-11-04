-- Prove2me | solution 1 for ThreeSum.HashFamily.hashMap_surjective_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:32.264118+00:00
-- url     : https://prove2.me/submissions/893eceb6-5cca-4e22-ab80-84f603bea6f2

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]
namespace ThreeSum.HashFamily
theorem _root_.solution {v : ι → σ → K} (hv : LinearIndependent K v) :
    Function.Surjective (hashMap v) := by
  classical
  let f := Fintype.linearCombination K v
  let B : (ι → K) →ₗ[K] (σ → K) →ₗ[K] K :=
    (dotProductEquiv K σ).toLinearMap.comp f
  have hi : Function.Injective B :=
    (dotProductEquiv K σ).injective.comp hv.fintypeLinearCombination_injective
  have hs : Function.Surjective B.flip := (LinearMap.flip_surjective_iff₁).mpr hi
  intro target
  obtain ⟨w, hw⟩ := hs (dotProductEquiv K ι target)
  refine ⟨w, ?_⟩
  funext i
  have he := congrArg (fun φ : Module.Dual K (ι → K) => φ (Pi.single i 1)) hw
  change dotProduct (v i) w = target i
  simpa [B, f, Fintype.linearCombination_apply] using he
end ThreeSum.HashFamily
