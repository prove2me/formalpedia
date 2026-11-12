-- Prove2me | solution 1 for ZeroOneExpansion.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:07:28.820209+00:00
-- url     : https://prove2.me/submissions/0439596d-d102-4c6f-b623-e647980d612d

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn
import Definitions.Def_ZeroOneExpansion_polyDim
import Definitions.Def_ZeroOneExpansion_edgeExpansion
import Definitions.Def_ZeroOneExpansion_Sn
import Theorems.Thm_ZeroOneExpansion_lemma_7
import Theorems.Thm_ZeroOneExpansion_lemma_12
import Theorems.Thm_ZeroOneExpansion_lemma_13

set_option autoImplicit false

namespace Aux_ZOE_thm14

open ZeroOneExpansion

lemma sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, (f i) ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ha0 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs_nn : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum_nn : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hs_nn
    have hih := ih hs_nn
    nlinarith

lemma diag_sum_le (n : ℕ) :
    ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℝ) ≤
      (12 : ℝ) ^ n * (((1 + Real.sqrt 6) ^ 2 / 12) ^ n) := by
  let s : ℝ := Real.sqrt 6
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 6
  have hs2 : s ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  let f : ℕ → ℝ := fun r => (n.choose r : ℝ) * s ^ r
  have hf_nn : ∀ r ∈ Finset.range (n + 1), 0 ≤ f r := fun r _ => by positivity
  have hf_sq : ∀ r, (f r) ^ 2 = (Acount n r r : ℝ) := by
    intro r
    have h1 : (f r) ^ 2 = (n.choose r : ℝ) * (n.choose r : ℝ) * (s ^ 2) ^ r := by
      dsimp only [f]; ring
    have h6 : (6 : ℝ) ^ r = (3 : ℝ) ^ r * (2 : ℝ) ^ r := by
      rw [← mul_pow]; norm_num
    rw [h1, hs2, h6, Acount]
    push_cast; ring
  have hsum_f : ∑ r ∈ Finset.range (n + 1), f r = (1 + s) ^ n := by
    rw [add_comm 1 s, add_pow]
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [f]
    ring
  calc ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℝ)
      = ∑ r ∈ Finset.range (n + 1), (f r) ^ 2 := by
        apply Finset.sum_congr rfl; intro r _; exact (hf_sq r).symm
    _ ≤ (∑ r ∈ Finset.range (n + 1), f r) ^ 2 := sum_sq_le_sq_sum _ f hf_nn
    _ = ((1 + s) ^ n) ^ 2 := by rw [hsum_f]
    _ = ((1 + s) ^ 2) ^ n := by rw [← pow_mul, mul_comm n 2, pow_mul]
    _ = (12 : ℝ) ^ n * (((1 + s) ^ 2 / 12) ^ n) := by
        rw [← mul_pow]
        congr 1
        ring

lemma pow_lt_one_of_pos_lt_one {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) {n : ℕ} (hn : 1 ≤ n) :
    b ^ n < 1 :=
  pow_lt_one₀ hb0.le hb1 (by omega)

lemma sq_div_four_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 / 4 ≤ Real.exp y := by
  have h1 : y / 2 + 1 ≤ Real.exp (y / 2) := Real.add_one_le_exp (y / 2)
  have hnn : 0 ≤ y / 2 + 1 := by linarith
  have hsq : (y / 2 + 1) ^ 2 ≤ Real.exp (y / 2) * Real.exp (y / 2) := by
    nlinarith
  have hexp : Real.exp (y / 2) * Real.exp (y / 2) = Real.exp y := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp] at hsq
  nlinarith

end Aux_ZOE_thm14

open ZeroOneExpansion Aux_ZOE_thm14

theorem solution :
    let β : ℝ := (1 + Real.sqrt 6) ^ 2 / 12
    β < 1 ∧
    (∀ n : ℕ, 1 ≤ n →
      edgeExpansion (Gn n) ≤ (((4 * n * β ^ n / (1 - β ^ n) : ℝ)) : EReal)) ∧
    (∀ᶠ n in Filter.atTop, edgeExpansion (Gn n) < 1) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop,
      edgeExpansion (Gn n) ≤ ((Real.exp (-c * (polyDim (Pn n) : ℝ)) : ℝ) : EReal) := by
  intro β
  have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have hs2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hβ_pos : 0 < β := by
    change 0 < (1 + Real.sqrt 6) ^ 2 / 12
    positivity
  have hβ_lt : β < 1 := by
    change (1 + Real.sqrt 6) ^ 2 / 12 < 1
    nlinarith
  have hbound : ∀ n : ℕ, 1 ≤ n →
      edgeExpansion (Gn n) ≤ (((4 * n * β ^ n / (1 - β ^ n) : ℝ)) : EReal) := by
    intro n hn
    obtain ⟨hSn_pos, hSn_eq_int, hSn_lt, hVn⟩ := ZeroOneExpansion.lemma_12 n hn
    obtain ⟨heb_eq, heb_le⟩ := ZeroOneExpansion.lemma_13 n hn
    have hadm : 1 ≤ (Sn n).ncard ∧
        2 * (Sn n).ncard ≤ Nat.card (Grunbaum2003.PolytopeVertex (Pn n)) := by
      omega
    have hinf : edgeExpansion (Gn n) ≤
        ((((edgeBoundary (Gn n) (Sn n)).ncard : ℝ) / ((Sn n).ncard : ℝ) : ℝ) : EReal) :=
      iInf₂_le (Sn n) hadm
    refine hinf.trans (EReal.coe_le_coe_iff.mpr ?_)
    let Dsum : ℝ := ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℝ)
    have hSn_real : ((Sn n).ncard : ℝ) = (12 : ℝ) ^ n - Dsum := by
      have hcast : (((Sn n).ncard : ℤ) : ℝ) =
          ((12 ^ n - ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℤ) : ℤ) : ℝ) :=
        congr_arg (Int.cast : ℤ → ℝ) hSn_eq_int
      simpa [Dsum] using hcast
    have hSn_rpos : 0 < ((Sn n).ncard : ℝ) := by exact_mod_cast hSn_pos
    have hβn_lt : β ^ n < 1 := pow_lt_one_of_pos_lt_one hβ_pos hβ_lt hn
    have h1mβ_pos : 0 < 1 - β ^ n := by linarith
    have heb_D : ((edgeBoundary (Gn n) (Sn n)).ncard : ℝ) ≤ 4 * (n : ℝ) * Dsum := by
      rw [heb_eq]; exact heb_le
    have hD_le : Dsum ≤ (12 : ℝ) ^ n * β ^ n := diag_sum_le n
    rw [div_le_div_iff₀ hSn_rpos h1mβ_pos]
    have hβn_nn : 0 ≤ β ^ n := le_of_lt (pow_pos hβ_pos n)
    have hn_nn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hSn_ge : (12 : ℝ) ^ n * (1 - β ^ n) ≤ ((Sn n).ncard : ℝ) := by
      have : (12 : ℝ) ^ n * (1 - β ^ n) = (12 : ℝ) ^ n - (12 : ℝ) ^ n * β ^ n := by ring
      linarith
    calc ((edgeBoundary (Gn n) (Sn n)).ncard : ℝ) * (1 - β ^ n)
        ≤ (4 * (n : ℝ) * ((12 : ℝ) ^ n * β ^ n)) * (1 - β ^ n) := by
          apply mul_le_mul_of_nonneg_right _ h1mβ_pos.le
          exact heb_D.trans (mul_le_mul_of_nonneg_left hD_le (by positivity))
      _ = (4 * (n : ℝ) * β ^ n) * ((12 : ℝ) ^ n * (1 - β ^ n)) := by ring
      _ ≤ (4 * (n : ℝ) * β ^ n) * ((Sn n).ncard : ℝ) :=
          mul_le_mul_of_nonneg_left hSn_ge (by positivity)
  let μ : ℝ := -Real.log β
  have hμ_pos : 0 < μ := by
    dsimp only [μ]
    linarith [Real.log_neg hβ_pos hβ_lt]
  have hβ_exp : ∀ n : ℕ, β ^ n = Real.exp (-μ * (n : ℝ)) := by
    intro n
    have hb : β = Real.exp (-μ) := by
      dsimp only [μ]
      rw [neg_neg, Real.exp_log hβ_pos]
    conv_lhs => rw [hb]
    rw [← Real.exp_nat_mul]
    ring_nf
  let c : ℝ := μ / 10
  have hc_pos : 0 < c := by dsimp only [c]; positivity
  let N₀ : ℕ := max 1 (max (Nat.ceil (1 / μ) + 1) (Nat.ceil (128 / μ ^ 2) + 1))
  have hev_both : ∀ n : ℕ, N₀ ≤ n →
      edgeExpansion (Gn n) ≤ ((Real.exp (-c * (polyDim (Pn n) : ℝ)) : ℝ) : EReal) ∧
      edgeExpansion (Gn n) < 1 := by
    intro n hnN
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hnN
    have hn_ceil1 : Nat.ceil (1 / μ) + 1 ≤ n :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hnN)
    have hn_ceil2 : Nat.ceil (128 / μ ^ 2) + 1 ≤ n :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hnN)
    have hn_r1 : 1 / μ < (n : ℝ) := by
      have hle : 1 / μ ≤ (Nat.ceil (1 / μ) : ℝ) := Nat.le_ceil (1 / μ)
      have hlt : (Nat.ceil (1 / μ) : ℝ) < (n : ℝ) := by exact_mod_cast hn_ceil1
      linarith
    have hn_r2 : 128 / μ ^ 2 < (n : ℝ) := by
      have hle : 128 / μ ^ 2 ≤ (Nat.ceil (128 / μ ^ 2) : ℝ) := Nat.le_ceil (128 / μ ^ 2)
      have hlt : (Nat.ceil (128 / μ ^ 2) : ℝ) < (n : ℝ) := by exact_mod_cast hn_ceil2
      linarith
    have hμn_gt1 : 1 < μ * (n : ℝ) := by
      have := (div_lt_iff₀ hμ_pos).mp hn_r1
      linarith
    have hβn_half : β ^ n ≤ 1 / 2 := by
      have hneg : -μ * (n : ℝ) = -(μ * (n : ℝ)) := by ring
      rw [hβ_exp n, hneg, Real.exp_neg]
      have hexp_ge : 2 ≤ Real.exp (μ * (n : ℝ)) := by
        have := Real.add_one_le_exp (μ * (n : ℝ))
        linarith
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hexp_ge
    have h8n_le1 : 8 * (n : ℝ) * Real.exp (-(μ / 2) * (n : ℝ)) ≤ 1 := by
      have hy : 0 ≤ (μ / 2) * (n : ℝ) := by positivity
      have hsq := sq_div_four_le_exp hy
      have h128 : 128 < μ ^ 2 * (n : ℝ) := by
        have hμ2 : 0 < μ ^ 2 := sq_pos_of_pos hμ_pos
        have := (div_lt_iff₀ hμ2).mp hn_r2
        linarith
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hexp_ge : 8 * (n : ℝ) ≤ Real.exp ((μ / 2) * (n : ℝ)) := by
        have hlhs : 8 * (n : ℝ) ≤ ((μ / 2) * (n : ℝ)) ^ 2 / 4 := by
          have : 128 * (n : ℝ) ≤ μ ^ 2 * (n : ℝ) ^ 2 := by nlinarith
          linarith
        exact hlhs.trans hsq
      have hprod : Real.exp ((μ / 2) * (n : ℝ)) * Real.exp (-(μ / 2) * (n : ℝ)) = 1 := by
        rw [← Real.exp_add]; simp
      have hexp_nn : 0 ≤ Real.exp (-(μ / 2) * (n : ℝ)) := le_of_lt (Real.exp_pos _)
      nlinarith
    have hdim : (polyDim (Pn n) : ℝ) = 4 * (n : ℝ) + 1 := by
      rw [ZeroOneExpansion.lemma_7 n hn1]; push_cast; ring
    have hexp_dim : Real.exp (-(μ / 2) * (n : ℝ)) ≤ Real.exp (-c * (polyDim (Pn n) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [hdim]
      dsimp only [c]
      have hn_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      nlinarith [hμ_pos, hn_r]
    have hsplit_exp : Real.exp (-μ * (n : ℝ)) =
        Real.exp (-(μ / 2) * (n : ℝ)) * Real.exp (-(μ / 2) * (n : ℝ)) := by
      rw [← Real.exp_add]; ring_nf
    have hmain_real : 4 * (n : ℝ) * β ^ n / (1 - β ^ n) ≤ Real.exp (-c * (polyDim (Pn n) : ℝ)) := by
      have h1m : 1 / 2 ≤ 1 - β ^ n := by linarith
      have hdiv_le : 4 * (n : ℝ) * β ^ n / (1 - β ^ n) ≤ 8 * (n : ℝ) * β ^ n := by
        rw [div_le_iff₀ (by linarith)]
        have hnn : 0 ≤ 4 * (n : ℝ) * β ^ n := by positivity
        nlinarith
      calc 4 * (n : ℝ) * β ^ n / (1 - β ^ n)
          ≤ 8 * (n : ℝ) * β ^ n := hdiv_le
        _ = (8 * (n : ℝ) * Real.exp (-(μ / 2) * (n : ℝ))) * Real.exp (-(μ / 2) * (n : ℝ)) := by
            rw [hβ_exp n, hsplit_exp]; ring
        _ ≤ 1 * Real.exp (-(μ / 2) * (n : ℝ)) := by
            exact mul_le_mul_of_nonneg_right h8n_le1 (le_of_lt (Real.exp_pos _))
        _ ≤ Real.exp (-c * (polyDim (Pn n) : ℝ)) := by linarith
    have he_le : edgeExpansion (Gn n) ≤ ((Real.exp (-c * (polyDim (Pn n) : ℝ)) : ℝ) : EReal) :=
      (hbound n hn1).trans (EReal.coe_le_coe_iff.mpr hmain_real)
    have hexp_lt1 : Real.exp (-c * (polyDim (Pn n) : ℝ)) < 1 := by
      rw [Real.exp_lt_one_iff, hdim]
      have hn_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      nlinarith
    have he_lt1 : edgeExpansion (Gn n) < 1 := by
      refine lt_of_le_of_lt he_le ?_
      change ((Real.exp (-c * (polyDim (Pn n) : ℝ)) : ℝ) : EReal) < ((1 : ℝ) : EReal)
      exact EReal.coe_lt_coe_iff.mpr hexp_lt1
    exact ⟨he_le, he_lt1⟩
  refine ⟨hβ_lt, hbound, ?_, ⟨c, hc_pos, ?_⟩⟩
  · exact Filter.eventually_atTop.mpr ⟨N₀, fun n hn => (hev_both n hn).2⟩
  · exact Filter.eventually_atTop.mpr ⟨N₀, fun n hn => (hev_both n hn).1⟩
