-- Prove2me | solution 1 for SumProduct.logEmbedding_mem_unitBox_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:54:16.283917+00:00
-- url     : https://prove2.me/submissions/55d64e5a-03b9-4227-8414-6c3108f4365a

import Mathlib
import Definitions.Def_SumProduct_Boxes
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
  NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} {u : (𝓞 K)ˣ} :
    logEmbedding K (Additive.ofMul u) ∈ unitBox K Y ↔ u ∈ boxMult K Y := by
  have hcomp : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      logEmbedding K (Additive.ofMul u) w = Real.log (w.val ((u : 𝓞 K) : K)) := by
    intro w
    rw [logEmbedding_component, IsTotallyReal.mult_eq, Nat.cast_one, one_mul]
  have hsum : ∑ w, logEmbedding K (Additive.ofMul u) w
      = -Real.log ((w₀ : InfinitePlace K) ((u : 𝓞 K) : K)) := by
    rw [sum_logEmbedding_component, IsTotallyReal.mult_eq, Nat.cast_one]; ring
  rw [mem_boxMult, unitBox, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ w
    by_cases hw : w = w₀
    · subst hw
      rw [hsum, abs_neg] at h2
      exact h2
    · rw [← hcomp ⟨w, hw⟩]
      exact h1 ⟨w, hw⟩
  · intro h
    refine ⟨fun w => ?_, ?_⟩
    · rw [hcomp w]
      exact h w.val
    · rw [hsum, abs_neg]
      exact h w₀
end SumProduct
