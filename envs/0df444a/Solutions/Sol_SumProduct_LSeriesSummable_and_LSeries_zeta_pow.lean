-- Prove2me | solution 1 for SumProduct.LSeriesSummable_and_LSeries_zeta_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:02:36.24268+00:00
-- url     : https://prove2.me/submissions/c2fbce91-ded8-40b0-a720-68bce60249d1

import Mathlib
import Definitions.Def_SumProduct_EulerBound
import Theorems.Thm_SumProduct_idealCountArith_apply_ne
attribute [local simp] SumProduct.idealCountArith_apply_ne

set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
open scoped LSeries.notation
open ArithmeticFunction
namespace SumProduct
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) (d : ℕ) :
    LSeriesSummable (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) s ∧
      LSeries (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) s
        = riemannZeta s ^ d := by
  -- Work in `ArithmeticFunction ℂ`: `Z = ↑ζ`, and `↑(ζ^m) = Z^m`.
  set Z : ArithmeticFunction ℂ :=
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) with hZdef
  have hcoeAF : ∀ m : ℕ,
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ m : ArithmeticFunction ℕ)
        : ArithmeticFunction ℂ) = Z ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero]; exact natCoe_one
    | succ m ih => rw [pow_succ, pow_succ, natCoe_mul, ih, hZdef]
  have hcoe : ∀ m : ℕ, (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ m) n : ℂ))
      = ↗(Z ^ m) := fun m => funext fun n => by rw [← hcoeAF m, natCoe_apply]
  have hZsum : LSeriesSummable (↗Z) s := by rw [hZdef]; exact LSeriesSummable_zeta_iff.mpr hs
  have hZS : LSeries (↗Z) s = riemannZeta s := by rw [hZdef]; exact LSeries_zeta_eq_riemannZeta hs
  have hδ : LSeriesSummable (↗(1 : ArithmeticFunction ℂ)) s := by
    rw [one_eq_delta]
    refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hpos.ne']; simp [LSeries.delta, hn]
  suffices h : ∀ m, LSeriesSummable (↗(Z ^ m)) s ∧ LSeries (↗(Z ^ m)) s = riemannZeta s ^ m by
    rw [hcoe d]; exact h d
  intro m
  induction m with
  | zero =>
    refine ⟨by rw [pow_zero]; exact hδ, ?_⟩
    rw [pow_zero, pow_zero, one_eq_delta, LSeries_delta]; exact Pi.one_apply s
  | succ m ih =>
    refine ⟨by rw [pow_succ]; exact LSeriesSummable_mul ih.1 hZsum, ?_⟩
    rw [pow_succ, LSeries_mul' ih.1 hZsum, ih.2, hZS, pow_succ]
end SumProduct
