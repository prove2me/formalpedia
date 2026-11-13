-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.Hypothesis.eta10_apply_sub_one_integral
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T15:46:16.872776+00:00
-- url     : https://prove2.me/submissions/92a38e36-5a52-4553-a8ff-b81c3497fe90

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **`η₁₀` is a virtual character of `G`** — real content of the 3002-threaded grid:
`η₁₀ = τ₃(ω₁₀)` (`eta_eq_tau_omega`), `ω₁₀ ∈ ZIrr W` (`omega_mem_ZIrr`), and `τ₃` preserves
virtual characters (`tau3_mem_ZIrr`). -/
theorem Hypothesis.eta10_mem_ZIrr [Finite G] (hyp : Hypothesis (G := G)) :
    hyp.eta10 ∈ ZIrr G := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
  exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)

/-- **Regularity of mixed products**: for `x ∈ W₁ ∖ {1}` and `y ∈ W₂ ∖ {1}` the product `x·y`
avoids `W₁ ∪ W₂` — otherwise one factor would lie in `W₁ ⊓ W₂ = ⊥`.  The membership feed of
`tau3_apply_of_regular` in the (1.10) congruence computations. -/
theorem Hypothesis.mul_notMem_W1_union_W2 (hyp : Hypothesis (G := G))
    {x y : G} (hx : x ∈ hyp.W1) (hy : y ∈ hyp.W2) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x * y ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := by
  rintro (hmem | hmem)
  · have hyW1 : y ∈ hyp.W1 := by
      have h := mul_mem (inv_mem hx) hmem
      rwa [inv_mul_cancel_left] at h
    have hbot : y ∈ hyp.W1 ⊓ hyp.W2 := ⟨hyW1, hy⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
    exact hy1 hbot
  · have hxW2 : x ∈ hyp.W2 := by
      have h := mul_mem hmem (inv_mem hy)
      rwa [mul_inv_cancel_right] at h
    have hbot : x ∈ hyp.W1 ⊓ hyp.W2 := ⟨hx, hxW2⟩
    rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hbot
    exact hx1 hbot

/-- **Peterfalvi (13.7), the (1.10) congruence for `η₁₀`**: for `y ∈ W₂^#`,
`η₁₀(y) ≡ 1 (mod (1 − ε))` in the algebraic integers, `ε` a primitive `q`-th root of unity.

Route: pick `x ∈ W₁^#`; `x` commutes with `y`, `x^q = 1`, and `η₁₀ ∈ ℤ[Irr G]`, so the
(1.10.a) congruence (`exists_integral_apply_sub_of_commute`) gives `η₁₀(xy) ≡ η₁₀(y)`.  The
product `xy` is `τ₃`-regular (`mul_notMem_W1_union_W2`), so `η₁₀(xy) = ω₁₀(xy)` ((3.2.c));
the (3.3) grid semantics factorize `ω₁₀(xy) = ω₁₀(x)·ω₁₀(y) = ω₁₀(x)` (issue 2033:
`omega_mul`, `omega_col_zero_apply_of_mem_W2`), a `q`-th root of unity
(`omega_pow_q_of_mem_W1`), which is `≡ 1 (mod (1 − ε))` by the geometric-sum identity. -/
theorem _root_.solution [Finite G] (hyp : Hypothesis (G := G))
    {ε : ℂ} (hε : IsPrimitiveRoot ε hyp.q) {y : G} (hyW2 : y ∈ hyp.W2) (hy1 : y ≠ 1) :
    ∃ z : ℂ, IsIntegral ℤ z ∧ hyp.eta10 y - 1 = (1 - ε) * z := by
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  -- pick `x ∈ W₁^#`
  obtain ⟨x, hxW1, hx1⟩ : ∃ x : G, x ∈ hyp.W1 ∧ x ≠ 1 := by
    have : Nontrivial ↥hyp.W1 := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [← hyp.q_eq_card_W1]; exact hyp.q_prime.one_lt)
    obtain ⟨x', hx'⟩ := exists_ne (1 : ↥hyp.W1)
    exact ⟨x', x'.2, fun h => hx' (Subtype.ext h)⟩
  -- `x^q = 1`
  have hxq : x ^ hyp.q = 1 := by
    have h1 : (⟨x, hxW1⟩ : ↥hyp.W1) ^ hyp.q = 1 := by
      rw [hyp.q_eq_card_W1]; exact pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
  -- (1.10.a): `η₁₀(xy) − η₁₀(y) = (1 − ε)·z₁`
  obtain ⟨z₁, hz₁int, hz₁⟩ :=
    OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute hyp.q_prime.pos hε
      hyp.eta10_mem_ZIrr hxq (hyp.W1_commutes_W2 x hxW1 y hyW2)
  -- `τ₃`-regular value: `η₁₀(xy) = ω₁₀(xy)`
  have hxyW : x * y ∈ hyp.W := mul_mem (hW1W hxW1) (hW2W hyW2)
  have hreg : hyp.eta10 (x * y)
      = hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x * y, hxyW⟩ := by
    rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
    exact hyp.tau3_apply_of_regular _ _ hxyW (hyp.mul_notMem_W1_union_W2 hxW1 hyW2 hx1 hy1)
  -- factorize: `ω₁₀(xy) = ω₁₀(x)·ω₁₀(y) = ω₁₀(x)` (issue-2033 grid semantics)
  have hfact : hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x * y, hxyW⟩
      = hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x, hW1W hxW1⟩ := by
    have hmul : (⟨x * y, hxyW⟩ : ↥hyp.W) = ⟨x, hW1W hxW1⟩ * ⟨y, hW2W hyW2⟩ := rfl
    rw [hmul, hyp.omega_mul,
      hyp.omega_col_zero_apply_of_mem_W2 _ ⟨y, hW2W hyW2⟩ hyW2, mul_one]
  -- `ω₁₀(x)` is a `q`-th root of unity: `= ε^k`
  have hpow : hyp.omega ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩ ⟨x, hW1W hxW1⟩ ^ hyp.q
      = 1 := hyp.omega_pow_q_of_mem_W1 _ _ ⟨x, hW1W hxW1⟩ hxW1
  have : NeZero hyp.q := ⟨hyp.q_prime.pos.ne'⟩
  obtain ⟨k, -, hk⟩ := hε.eq_pow_of_pow_eq_one hpow
  -- `ε^k − 1 = (1 − ε)·z₂` with `z₂` integral (geometric sum)
  have hε_mem : ε ∈ integralClosure ℤ ℂ := hε.isIntegral hyp.q_prime.pos
  have hz₂int : IsIntegral ℤ (-(∑ i ∈ Finset.range k, ε ^ i)) :=
    (Subalgebra.sum_mem _ (fun i _ => Subalgebra.pow_mem _ hε_mem i) :
      IsIntegral ℤ (∑ i ∈ Finset.range k, ε ^ i)).neg
  have hz₂ : ε ^ k - 1 = (1 - ε) * (-(∑ i ∈ Finset.range k, ε ^ i)) := by
    rw [← geom_sum_mul ε k]; ring
  -- combine: `η₁₀(y) − 1 = (η₁₀(xy) − (1−ε)z₁) − 1 = (ε^k − 1) − (1−ε)z₁`
  refine ⟨-(∑ i ∈ Finset.range k, ε ^ i) - z₁, hz₂int.sub hz₁int, ?_⟩
  have hyval : hyp.eta10 y = hyp.eta10 (x * y) - (1 - ε) * z₁ := by linear_combination -hz₁
  rw [hyval, hreg, hfact, ← hk]
  linear_combination hz₂

end OddOrder.Peterfalvi.S15
