-- Prove2me | solution 1 for ShorAlgorithms.DiscreteLog.good_output_prob_ge
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:52:59.299145+00:00
-- url     : https://prove2.me/submissions/78c15b14-9d18-49a3-940e-3173c6889b80

import Mathlib
import Definitions.Def_ShorAlgorithms_DiscreteLog_outcomeProb
import Definitions.Def_ShorAlgorithms_DiscreteLog_IsGood
namespace AShorLower

lemma sum_real (M : ℕ) : ∑ j ∈ Finset.range M, (j : ℝ) = (M : ℝ) * (M - 1) / 2 := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_sq (M : ℕ) : ∑ j ∈ Finset.range M, (j : ℝ) ^ 2 = (M : ℝ) * (M - 1) * (2 * M - 1) / 6 := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma centered_sq (M : ℕ) :
    ∑ j ∈ Finset.range M, ((j : ℝ) - ((M : ℝ) - 1) / 2) ^ 2 = (M : ℝ) * ((M : ℝ) ^ 2 - 1) / 12 := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [sum_sq, sum_real]
  ring

lemma geometric_lower (M : ℕ) (θ : ℝ) :
    (M : ℝ) * (1 - θ ^ 2 * ((M : ℝ) ^ 2 - 1) / 24) ≤
      ‖∑ j ∈ Finset.range M, Complex.exp ((((j : ℝ) * θ) : ℝ) * Complex.I)‖ := by
  let C : ℝ := ((M : ℝ) - 1) / 2
  have he : (∑ j ∈ Finset.range M, Complex.exp ((((j : ℝ) * θ) : ℝ) * Complex.I)) =
      Complex.exp (((C * θ : ℝ) : ℂ) * Complex.I) *
        ∑ j ∈ Finset.range M, Complex.exp (((((j : ℝ) - C) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc
    _ = ∑ j ∈ Finset.range M, (1 - (((j : ℝ) - C) * θ) ^ 2 / 2) := by
      simp only [mul_pow, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
        ← Finset.sum_div, ← Finset.sum_mul]
      rw [show (∑ j ∈ Finset.range M, ((j : ℝ) - C) ^ 2) = (M : ℝ) * ((M : ℝ) ^ 2 - 1) / 12 from centered_sq M]
      ring
    _ ≤ ∑ j ∈ Finset.range M, Real.cos (((j : ℝ) - C) * θ) :=
      Finset.sum_le_sum (fun j _ => Real.one_sub_sq_div_two_le_cos)
    _ = (∑ j ∈ Finset.range M, Complex.exp (((((j : ℝ) - C) * θ : ℝ) : ℂ) * Complex.I)).re := by
      simp only [Complex.re_sum, Complex.exp_ofReal_mul_I_re]
    _ ≤ _ := Complex.re_le_norm _

lemma analytic_bound (M : ℕ) (θ R Q : ℝ) (hR : 0 < R) (hQ : 1000 * R ≤ Q)
    (hl : Q - R ≤ M * R) (hu : M * R ≤ Q + R)
    (hθ : |θ| ≤ Real.pi * R / Q) :
    (289 / 500 : ℝ) * Q / R ≤ ‖∑ j ∈ Finset.range M, Complex.exp ((((j : ℝ) * θ) : ℝ) * Complex.I)‖ := by
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hratio : (M : ℝ) * R / Q ≤ 1001 / 1000 := by
    apply (div_le_iff₀ hQ0).mpr
    nlinarith
  have hthM : |θ| * M ≤ Real.pi * (1001 / 1000) := by
    calc |θ| * M ≤ (Real.pi * R / Q) * M := mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _)
      _ = Real.pi * ((M : ℝ) * R / Q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio Real.pi_pos.le
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hsq := mul_self_le_mul_self (show 0 ≤ |θ| * (M : ℝ) by positivity) hthM
  have hθM : θ ^ 2 * (M : ℝ) ^ 2 ≤ 101 / 10 := by
    nlinarith [sq_abs θ]
  have hc : 139 / 240 ≤ 1 - θ ^ 2 * ((M : ℝ) ^ 2 - 1) / 24 := by nlinarith [sq_nonneg θ]
  have hm : (999 / 1000 : ℝ) * Q / R ≤ M := by
    apply (div_le_iff₀ hR).mpr
    nlinarith
  calc
    (289 / 500 : ℝ) * Q / R ≤ (139 / 240) * ((999 / 1000 : ℝ) * Q / R) := by
      have hQR : 0 ≤ Q / R := by positivity
      calc (289 / 500 : ℝ) * Q / R = (289 / 500) * (Q / R) := by ring
        _ ≤ ((139 / 240) * (999 / 1000)) * (Q / R) :=
          mul_le_mul_of_nonneg_right (by norm_num) hQR
        _ = _ := by ring
    _ ≤ (139 / 240) * M := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ ≤ (M : ℝ) * (1 - θ ^ 2 * ((M : ℝ) ^ 2 - 1) / 24) := by nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg M)]
    _ ≤ _ := geometric_lower M θ

lemma shifted_norm (q r k c M : ℕ) (d : ℤ) (hq : 0 < q) :
    ‖∑ b ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I *
      (((b * r + k : ℕ)) : ℂ) * (c : ℂ) / (q : ℂ))‖ =
    ‖∑ b ∈ Finset.range M, Complex.exp ((((b : ℝ) *
      (2 * Real.pi * ((r : ℝ) * c - (d : ℝ) * q) / q) : ℝ) : ℂ) * Complex.I)‖ := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : (∑ b ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I *
      (((b * r + k : ℕ)) : ℂ) * (c : ℂ) / (q : ℂ))) =
      Complex.exp ((((2 * Real.pi * (k : ℝ) * c / q : ℝ)) : ℂ) * Complex.I) *
      ∑ b ∈ Finset.range M, Complex.exp ((((b : ℝ) *
      (2 * Real.pi * ((r : ℝ) * c - (d : ℝ) * q) / q) : ℝ) : ℂ) * Complex.I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨(b : ℤ) * d, ?_⟩
    push_cast
    field_simp
    <;> ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma series_bounds {q r k : ℕ} (hr : 0 < r) (hk : k < r) (hkq : k < q) :
    (q : ℝ) - r ≤ (((q - k - 1) / r + 1 : ℕ) : ℝ) * r ∧
      (((q - k - 1) / r + 1 : ℕ) : ℝ) * r ≤ (q : ℝ) + r := by
  let M := (q - k - 1) / r + 1
  have hb : q - k - 1 < M * r := by
    simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ (q - k - 1) hr
  have ha := Nat.div_mul_le_self (q - k - 1) r
  have he : M * r = ((q - k - 1) / r) * r + r := by dsimp [M]; ring
  have hl : q ≤ M * r + r := by omega
  have hu : M * r ≤ q + r := by omega
  have hl' : (q : ℝ) ≤ (M : ℝ) * r + r := by exact_mod_cast hl
  have hu' : (M : ℝ) * r ≤ (q : ℝ) + r := by exact_mod_cast hu
  constructor <;> change _ <;> dsimp [M] at * <;> linarith

lemma enough_samples {n q r : ℕ} (hn : 1000 ≤ n) (hrn : r ≤ n) (hnq : n ^ 2 ≤ q) : 1000 * r ≤ q := by
  calc 1000 * r ≤ 1000 * n := Nat.mul_le_mul_left _ hrn
    _ ≤ n * n := Nat.mul_le_mul_right _ hn
    _ = n ^ 2 := by ring
    _ ≤ q := hnq

end AShorLower
open ShorAlgorithms.DiscreteLog ShorAlgorithms.Shared
namespace AShorLog

lemma sqrt_inv_sq (q : ℕ) : ((Real.sqrt q : ℝ) : ℂ)⁻¹ * ((Real.sqrt q : ℝ) : ℂ)⁻¹ = (q : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg q)]
  rfl

lemma sum_trunc {N q : ℕ} (hNq : N ≤ q) (F : ℕ → ℂ) :
    (∑ i : Fin q, if (i : ℕ) < N then F i else 0) = ∑ i ∈ Finset.range N, F i := by
  classical
  rw [← Finset.sum_range (fun i => if i < N then F i else 0)]
  calc
    _ = ∑ i ∈ Finset.range N, if i < N then F i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hNq)
      intro i hi hin
      simp only [Finset.mem_range] at hin
      simp [hin]
    _ = _ := by apply Finset.sum_congr rfl; intro i hi; simp [Finset.mem_range.mp hi]

lemma power_congruence (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (a b r k : ℕ) :
    (g ^ k = g ^ a * (g ^ r)⁻¹ ^ b) ↔
      (a : ℤ) - (r : ℤ) * (b : ℤ) ≡ (k : ℤ) [ZMOD ((p : ℤ) - 1)] := by
  have he : g ^ ((a : ℤ) - (r : ℤ) * b) = g ^ a * (g ^ r)⁻¹ ^ b := by
    rw [zpow_sub, zpow_natCast, zpow_mul, zpow_natCast, zpow_natCast, inv_pow]
  rw [← he, ← zpow_natCast g k, eq_comm, zpow_eq_zpow_iff_modEq, hg, Nat.cast_sub hp.out.one_le]
  simp only [Nat.cast_one]

lemma coefficient (p q a b c d : ℕ) :
    (((p - 1 : ℕ) : ℂ))⁻¹ *
      (((Real.sqrt q : ℝ) : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (c : ℂ) / (q : ℂ))) *
      (((Real.sqrt q : ℝ) : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) * (d : ℂ) / (q : ℂ))) =
    (1 / (((p - 1 : ℕ) : ℂ) * (q : ℂ))) * Complex.exp
      (2 * Real.pi * Complex.I / (q : ℂ) * ((a : ℂ) * c + (b : ℂ) * d)) := by
  calc
    _ = (((p - 1 : ℕ) : ℂ))⁻¹ *
      (((Real.sqrt q : ℝ) : ℂ)⁻¹ * ((Real.sqrt q : ℝ) : ℂ)⁻¹) *
      (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (c : ℂ) / (q : ℂ)) *
       Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) * (d : ℂ) / (q : ℂ))) := by ring
    _ = _ := by
      rw [sqrt_inv_sq, ← Complex.exp_add]
      simp only [one_div, mul_inv]
      congr 2
      ring

lemma amplitude (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r q k : ℕ) (hpq : p < q) (c d : Fin q) :
    finalState p g (g ^ r) q (c, d, g ^ k) =
      (1 / (((p : ℂ) - 1) * (q : ℂ))) *
        ∑ a ∈ Finset.range (p - 1), ∑ b ∈ Finset.range (p - 1),
          if (a : ℤ) - (r : ℤ) * (b : ℤ) ≡ (k : ℤ) [ZMOD ((p : ℤ) - 1)] then
            Complex.exp (2 * Real.pi * Complex.I / (q : ℂ) *
              ((a : ℂ) * ((c : ℕ) : ℂ) + (b : ℂ) * ((d : ℕ) : ℂ)))
          else 0 := by
  classical
  let F (a b : ℕ) : ℂ := if (a : ℤ) - (r : ℤ) * (b : ℤ) ≡ (k : ℤ) [ZMOD ((p : ℤ) - 1)] then
    Complex.exp (2 * Real.pi * Complex.I / (q : ℂ) * ((a : ℂ) * (c : ℕ) + (b : ℂ) * (d : ℕ))) else 0
  have hN : p - 1 ≤ q := by omega
  have he : finalState p g (g ^ r) q (c, d, g ^ k) =
      (1 / (((p - 1 : ℕ) : ℂ) * (q : ℂ))) * ∑ a : Fin q,
        if (a : ℕ) < p - 1 then ∑ b : Fin q, if (b : ℕ) < p - 1 then F a b else 0 else 0 := by
    simp only [finalState, preFourierState, fourierMatrix, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : (a : ℕ) < p - 1
    · simp only [ha, true_and, if_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : (b : ℕ) < p - 1
      · simp only [hb, true_and, if_true, power_congruence p g hg, F]
        split_ifs
        · exact coefficient p q a b c d
        · simp
      · simp [hb]
    · simp [ha]
  rw [he, sum_trunc hN (fun a => ∑ b : Fin q, if (b : ℕ) < p - 1 then F a b else 0)]
  have hb (a : ℕ) := sum_trunc hN (F a)
  simp_rw [hb]
  simp only [Nat.cast_sub hp.out.one_le, Nat.cast_one, F]

end AShorLog
open ShorAlgorithms.DiscreteLog
namespace AShorLogLower

lemma exp_difference (x y : ℝ) :
    ‖Complex.exp (((x + y : ℝ) : ℂ) * Complex.I) - Complex.exp ((x : ℂ) * Complex.I)‖ ≤ |y| := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, ← mul_sub_one, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [mul_comm, Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := y))

lemma perturbed_geometric (M : ℕ) (θ : ℝ) (δ : ℕ → ℝ)
    (hθ : |θ| * M ≤ Real.pi) (hδ : ∀ b < M, |δ b| ≤ Real.pi / 12) :
    (M : ℝ) / 4 ≤ ‖∑ b ∈ Finset.range M, Complex.exp ((((b : ℝ) * θ + δ b : ℝ) : ℂ) * Complex.I)‖ := by
  let S : ℂ := ∑ b ∈ Finset.range M, Complex.exp ((((b : ℝ) * θ : ℝ) : ℂ) * Complex.I)
  let P : ℂ := ∑ b ∈ Finset.range M, Complex.exp ((((b : ℝ) * θ + δ b : ℝ) : ℂ) * Complex.I)
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hs := mul_self_le_mul_self (show 0 ≤ |θ| * (M : ℝ) by positivity) hθ
  have hθM : θ ^ 2 * (M : ℝ) ^ 2 ≤ Real.pi ^ 2 := by nlinarith [sq_abs θ]
  have hc : (7 / 12 : ℝ) ≤ 1 - θ ^ 2 * ((M : ℝ) ^ 2 - 1) / 24 := by nlinarith [sq_nonneg θ]
  have hS : (7 / 12 : ℝ) * M ≤ ‖S‖ := by
    have := AShorLower.geometric_lower M θ
    have hmul := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg M)
    dsimp [S]
    nlinarith
  have hdiff : ‖P - S‖ ≤ (M : ℝ) * (Real.pi / 12) := by
    dsimp [P, S]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ b ∈ Finset.range M, ‖Complex.exp ((((b : ℝ) * θ + δ b : ℝ) : ℂ) * Complex.I) -
        Complex.exp ((((b : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ := norm_sum_le _ _
      _ ≤ ∑ b ∈ Finset.range M, Real.pi / 12 := by
        apply Finset.sum_le_sum
        intro b hb
        exact (exp_difference ((b : ℝ) * θ) (δ b)).trans (hδ b (Finset.mem_range.mp hb))
      _ = _ := by simp
  have hdiff' : ‖P - S‖ ≤ (M : ℝ) / 3 := by
    have hmul := mul_le_mul_of_nonneg_left Real.pi_lt_four.le (Nat.cast_nonneg M)
    nlinarith
  have htri := norm_sub_le P (P - S)
  rw [sub_sub_cancel] at htri
  change (M : ℝ) / 4 ≤ ‖P‖
  linarith


lemma residue_rep (q z : ℤ) : ∃ u : ℤ, z = symmRes q z + u * q := by
  have he := Int.emod_add_ediv_mul z q
  unfold symmRes
  split_ifs
  · refine ⟨z / q, ?_⟩
    nlinarith
  · refine ⟨z / q + 1, ?_⟩
    nlinarith

lemma condition {N a : ℕ} (ha : a < N) (r b k : ℕ) :
    ((a : ℤ) - (r : ℤ) * b ≡ (k : ℤ) [ZMOD (N : ℤ)]) ↔ a = (r * b + k) % N := by
  have he : ((a : ℤ) - (r : ℤ) * b ≡ (k : ℤ) [ZMOD (N : ℤ)]) ↔
      ((a : ℤ) ≡ ((r * b + k : ℕ) : ℤ) [ZMOD (N : ℤ)]) := by
    constructor
    · intro h
      have h' := h.add_right ((r : ℤ) * b)
      simpa only [sub_add_cancel, Nat.cast_add, Nat.cast_mul, add_comm (k : ℤ) ((r : ℤ) * b)] using h'
    · intro h
      have h' := h.sub_right ((r : ℤ) * b)
      simpa only [Nat.cast_add, Nat.cast_mul, add_sub_cancel_left] using h'
  rw [he, Int.natCast_modEq_iff]
  change a % N = (r * b + k) % N ↔ _
  rw [Nat.mod_eq_of_lt ha]

lemma collapse (N r k : ℕ) (hN : 0 < N) (F : ℕ → ℕ → ℂ) :
    (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
      if ((a : ℤ) - (r : ℤ) * b ≡ (k : ℤ) [ZMOD (N : ℤ)]) then F a b else 0) =
      ∑ b ∈ Finset.range N, F ((r * b + k) % N) b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = ∑ a ∈ Finset.range N, if a = (r * b + k) % N then F a b else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [condition (Finset.mem_range.mp ha)]
    _ = _ := by simp [Finset.sum_ite_eq', Nat.mod_lt _ hN]

lemma phase_algebra (N q r k c d b : ℕ) (hN : 0 < N) (z u j : ℤ)
    (hz : (c : ℤ) * N = z + u * q) :
    let a : ℕ := (r * b + k) % N
    let s : ℝ := (r : ℝ) * c + d - (r : ℝ) / N * z - (j : ℝ) * q
    (a : ℝ) * c + (b : ℝ) * d =
      (b : ℝ) * s + (k : ℝ) * c + ((a : ℝ) - k) * z / N +
        (q : ℝ) * ((b : ℝ) * j - (((r * b + k) / N : ℕ) : ℝ) * u) := by
  dsimp only
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (((r * b + k) % N : ℕ) : ℝ) + (N : ℝ) * (((r * b + k) / N : ℕ) : ℝ) =
      (r : ℝ) * b + k := by exact_mod_cast Nat.mod_add_div (r * b + k) N
  have hz' : (c : ℝ) * N = (z : ℝ) + (u : ℝ) * q := by exact_mod_cast hz
  apply (mul_left_cancel₀ hN0)
  field_simp
  linear_combination ((N : ℝ) * c - z) * hm - (N : ℝ) * (((r * b + k) / N : ℕ) : ℝ) * hz'

lemma phase_norm (N q r k c d : ℕ) (hN : 0 < N) (hq : 0 < q) (z u j : ℤ)
    (hz : (c : ℤ) * N = z + u * q) :
    let C : ℝ := ((N : ℝ) - 1) / 2
    let s : ℝ := (r : ℝ) * c + d - (r : ℝ) / N * z - (j : ℝ) * q
    let θ : ℝ := 2 * Real.pi / q * s
    let δ : ℕ → ℝ := fun b => 2 * Real.pi / q * (((((r * b + k) % N : ℕ) : ℝ) - C) * z / N)
    ‖∑ b ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I / (q : ℂ) *
      (((((r * b + k) % N : ℕ)) : ℂ) * (c : ℂ) + (b : ℂ) * d))‖ =
    ‖∑ b ∈ Finset.range N, Complex.exp ((((b : ℝ) * θ + δ b : ℝ) : ℂ) * Complex.I)‖ := by
  intro C s θ δ
  let κ : ℝ := 2 * Real.pi / q * ((k : ℝ) * c + (C - k) * z / N)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (∑ b ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I / (q : ℂ) *
      (((((r * b + k) % N : ℕ)) : ℂ) * (c : ℂ) + (b : ℂ) * d))) =
      Complex.exp ((κ : ℂ) * Complex.I) *
        ∑ b ∈ Finset.range N, Complex.exp ((((b : ℝ) * θ + δ b : ℝ) : ℂ) * Complex.I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨(b : ℤ) * j - (((r * b + k) / N : ℕ) : ℤ) * u, ?_⟩
    have halg := phase_algebra N q r k c d b hN z u j hz
    have hreal : (2 * Real.pi / q) * (((((r * b + k) % N : ℕ)) : ℝ) * c + (b : ℝ) * d) =
        κ + ((b : ℝ) * θ + δ b) +
          ((b : ℝ) * j - (((r * b + k) / N : ℕ) : ℝ) * u) * (2 * Real.pi) := by
      rw [halg]
      dsimp [κ, θ, δ, s]
      field_simp
      <;> ring
    have hc := congrArg (fun t : ℝ => (t : ℂ) * Complex.I) hreal
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
      Complex.ofReal_intCast, Complex.ofReal_ofNat] at hc ⊢
    convert hc using 1 <;> ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma residual_bounds (N q r k : ℕ) (hN : 0 < N) (hq : 0 < q) (hNq : N ≤ q) (s z : ℝ)
    (hs : |s| ≤ 1 / 2) (hz : |z| ≤ (q : ℝ) / 12) :
    let C : ℝ := ((N : ℝ) - 1) / 2
    let θ : ℝ := 2 * Real.pi / q * s
    let δ : ℕ → ℝ := fun b => 2 * Real.pi / q * (((((r * b + k) % N : ℕ) : ℝ) - C) * z / N)
    |θ| * N ≤ Real.pi ∧ ∀ b < N, |δ b| ≤ Real.pi / 12 := by
  intro C θ δ
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNq' : (N : ℝ) ≤ q := by exact_mod_cast hNq
  have hpos : 0 < 2 * Real.pi / (q : ℝ) := by positivity
  constructor
  · dsimp [θ]
    rw [abs_mul, abs_of_pos hpos]
    calc (2 * Real.pi / (q : ℝ)) * |s| * N ≤ (2 * Real.pi / (q : ℝ)) * (1 / 2) * q := by gcongr
      _ = Real.pi := by field_simp
  · intro b hb
    have ha := Nat.mod_lt (r * b + k) hN
    have ha' : (((r * b + k) % N : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ (((r * b + k) % N : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcenter : |((r * b + k) % N : ℕ) - C| ≤ (N : ℝ) / 2 := by
      rw [abs_le]
      dsimp [C]
      constructor <;> linarith
    dsimp [δ]
    rw [abs_mul, abs_of_pos hpos, abs_div, abs_of_pos hN', abs_mul]
    calc (2 * Real.pi / (q : ℝ)) * (|((r * b + k) % N : ℕ) - C| * |z| / N)
        ≤ (2 * Real.pi / (q : ℝ)) * (((N : ℝ) / 2) * ((q : ℝ) / 12) / N) := by gcongr
      _ = Real.pi / 12 := by field_simp

lemma generator_rep (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (y : (ZMod p)ˣ) : ∃ k : ℕ, k < p - 1 ∧ g ^ k = y := by
  classical
  let f : Fin (p - 1) → (ZMod p)ˣ := fun k => g ^ (k : ℕ)
  have hi : Function.Injective f := by
    intro a b he
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := g) (by simpa [hg] using a.isLt) (by simpa [hg] using b.isLt) he
  have hcard : Fintype.card (Fin (p - 1)) = Fintype.card (ZMod p)ˣ := by
    rw [Fintype.card_fin, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  obtain ⟨k, hk⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hi, hcard⟩).2 y
  exact ⟨k, k.isLt, hk⟩

lemma state_lower (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r q : ℕ) (hpq : p < q) (c d : Fin q) (hgood : IsGood p q r c d) (y : (ZMod p)ˣ) :
    1 / (16 * (q : ℝ) ^ 2) ≤ outcomeProb p g (g ^ r) q c d y := by
  classical
  obtain ⟨k, hk, rfl⟩ := generator_rep p g hg y
  let N := p - 1
  have hN : 0 < N := by dsimp [N]; have := hp.out.two_le; omega
  have hq : 0 < q := lt_trans hp.out.pos hpq
  have hNq : N ≤ q := by dsimp [N]; omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  let z : ℤ := symmRes (q : ℤ) ((c : ℕ) * (N : ℤ))
  obtain ⟨u, hu⟩ := residue_rep (q : ℤ) ((c : ℕ) * (N : ℤ))
  obtain ⟨j, hj⟩ := hgood.1
  let s : ℝ := (r : ℝ) * (c : ℕ) + (d : ℕ) - (r : ℝ) / N * z - (j : ℝ) * q
  have hs : |s| ≤ 1 / 2 := by
    simpa [s, z, N, phaseT, Nat.cast_sub hp.out.one_le] using hj
  have hz : |(z : ℝ)| ≤ (q : ℝ) / 12 := by
    simpa [z, N, Nat.cast_sub hp.out.one_le] using hgood.2
  let S : ℂ := ∑ b ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I / (q : ℂ) *
      (((((r * b + k) % N : ℕ)) : ℂ) * ((c : ℕ) : ℂ) + (b : ℂ) * (d : ℕ)))
  have hS : (N : ℝ) / 4 ≤ ‖S‖ := by
    dsimp [S]
    rw [phase_norm N q r k c d hN hq z u j hu]
    have hh := residual_bounds N q r k hN hq hNq s (z : ℝ) hs hz
    exact perturbed_geometric N _ _ hh.1 hh.2
  have hamp : ShorAlgorithms.DiscreteLog.finalState p g (g ^ r) q (c, d, g ^ k) =
      (1 / ((N : ℂ) * q)) * S := by
    rw [AShorLog.amplitude p g hg r q k hpq c d]
    have hNc : (p : ℂ) - 1 = N := by simp [N, Nat.cast_sub hp.out.one_le]
    have hNz : (p : ℤ) - 1 = N := by simp [N, Nat.cast_sub hp.out.one_le]
    rw [hNc, hNz, collapse N r k hN]
  rw [outcomeProb, hamp, norm_mul, norm_div, norm_one, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hzS : 1 / (4 * (q : ℝ)) ≤ (1 / ((N : ℝ) * q)) * ‖S‖ := by
    have h := mul_le_mul_of_nonneg_left hS (show 0 ≤ (1 : ℝ) / ((N : ℝ) * q) by positivity)
    have he : (1 / ((N : ℝ) * q)) * ((N : ℝ) / 4) = 1 / (4 * (q : ℝ)) := by field_simp
    rw [he] at h
    exact h
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 1 / (4 * (q : ℝ))) hzS
  have he : (1 / (4 * (q : ℝ))) * (1 / (4 * (q : ℝ))) = 1 / (16 * (q : ℝ) ^ 2) := by ring
  simpa only [he, pow_two] using hsq

end AShorLogLower
open ShorAlgorithms.DiscreteLog
namespace AShorLogLower
lemma state_weak (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r q : ℕ) (hpq : p < q) (c d : Fin q) (hgood : IsGood p q r c d) (y : (ZMod p)ˣ) :
    1 / (20 * (q : ℝ) ^ 2) ≤ outcomeProb p g (g ^ r) q c d y := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_trans hp.out.pos hpq)
  apply le_trans _ (state_lower p g hg r q hpq c d hgood y)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg (q : ℝ)]

lemma good_pair_sum (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r q : ℕ) (hpq : p < q) (c d : Fin q) (hgood : IsGood p q r c d) :
    ((p : ℝ) - 1) / (20 * (q : ℝ) ^ 2) ≤ ∑ y : (ZMod p)ˣ, outcomeProb p g (g ^ r) q c d y := by
  classical
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod p)ˣ))
    (fun y _ => state_weak p g hg r q hpq c d hgood y)
  simpa [ZMod.card_units_eq_totient, Nat.totient_prime hp.out, Nat.cast_sub hp.out.one_le,
    div_eq_mul_inv] using hh

lemma q_bound (p q l : ℕ) [hp : Fact p.Prime] (hq : q = 2 ^ l) (hpq : p < q) (hqp : q < 2 * p) :
    q ≤ 2 * (p - 1) := by
  have hp2 := hp.out.two_le
  cases l with
  | zero => simp at hq; omega
  | succ l => rw [pow_succ] at hq; omega

lemma numeric_bound (p q l : ℕ) [hp : Fact p.Prime] (hq : q = 2 ^ l) (hpq : p < q) (hqp : q < 2 * p) :
    1 / (40 * (q : ℝ)) ≤ ((p : ℝ) - 1) / (20 * (q : ℝ)^2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_trans hp.out.pos hpq)
  have h := q_bound p q l hq hpq hqp
  have h' : (q : ℝ) ≤ 2 * ((p : ℝ) - 1) := by
    have hh : (q : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by exact_mod_cast h
    simpa [Nat.cast_sub hp.out.one_le] using hh
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 40 * q) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right h' hq0.le]

lemma good_c_sum (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r q : ℕ) (hpq : p < q) (c : Fin q) (hc : ∃ d : Fin q, IsGood p q r c d) :
    ((p : ℝ) - 1) / (20 * (q : ℝ)^2) ≤ ∑ d : Fin q, ∑ y : (ZMod p)ˣ, outcomeProb p g (g^r) q c d y := by
  classical
  obtain ⟨d, hd⟩ := hc
  apply le_trans (good_pair_sum p g hg r q hpq c d hd)
  apply Finset.single_le_sum (fun j _ => ?_) (Finset.mem_univ d)
  exact Finset.sum_nonneg (fun y _ => sq_nonneg _)
end AShorLogLower

open ShorAlgorithms.DiscreteLog
namespace AShorLogCount

lemma good_d (p q r : ℕ) (hq : 0 < q) (c : Fin q)
    (hc : |(symmRes (q : ℤ) ((c : ℕ) * ((p : ℤ) - 1)) : ℝ)| ≤ (q : ℝ) / 12) :
    ∃ d : Fin q, IsGood p q r c d := by
  let t : ℝ := (r : ℝ) * (c : ℕ) - (r : ℝ) / ((p : ℝ) - 1) *
    (symmRes (q : ℤ) ((c : ℕ) * ((p : ℤ) - 1)) : ℝ)
  let z : ℤ := round (-t)
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hz0 := Int.emod_nonneg z (ne_of_gt hqz)
  have hzq := Int.emod_lt_of_pos z hqz
  let d : Fin q := ⟨(z % (q : ℤ)).toNat, by omega⟩
  refine ⟨d, ⟨?_, hc⟩⟩
  refine ⟨-(z / (q : ℤ)), ?_⟩
  have hdiv := Int.emod_add_ediv_mul z (q : ℤ)
  have hd : ((d : ℕ) : ℤ) = z % (q : ℤ) := Int.toNat_of_nonneg hz0
  have he : (d : ℕ) + (z / (q : ℤ) : ℤ) * (q : ℝ) = (z : ℝ) := by
    have hz := congrArg (fun x : ℤ => (x : ℝ)) hdiv
    push_cast at hz
    have hd' := congrArg (fun x : ℤ => (x : ℝ)) hd
    push_cast at hd'
    linarith
  have hab := abs_sub_round (-t)
  have ht : phaseT p q r c d - ((-(z / (q : ℤ)) : ℤ) : ℝ) * q = -(-t - z) := by
    simp only [phaseT, Int.cast_neg]
    dsimp [t]
    linarith
  rw [ht, abs_neg]
  exact hab

lemma bezout (N q : ℕ) :
    (N : ZMod q) * (Nat.gcdA N q : ℤ) = (Nat.gcd N q : ℕ) := by
  have h := congrArg (fun x : ℤ => (x : ZMod q)) (Nat.gcd_eq_gcd_ab N q)
  simpa using h.symm

lemma kernel_step (N q : ℕ) :
    (N : ZMod q) * ((q / Nat.gcd N q : ℕ) : ZMod q) = 0 := by
  have he : N * (q / Nat.gcd N q) = (N / Nat.gcd N q) * q := by
    calc N * (q / Nat.gcd N q)
      = ((N / Nat.gcd N q) * Nat.gcd N q) * (q / Nat.gcd N q) := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left N q)]
      _ = (N / Nat.gcd N q) * q := by rw [mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right N q)]
  have h := congrArg (fun x : ℕ => (x : ZMod q)) he
  simpa only [Nat.cast_mul, ZMod.natCast_self, mul_zero] using h

lemma simple_residue (q v w : ℕ) (hq : 0 < q) (hw : w < q)
    (hh : 2 * w ≤ q) (he : (v : ZMod q) = w) : symmRes (q : ℤ) (v : ℤ) = w := by
  have hm : v % q = w := by
    have := congrArg ZMod.val he
    simpa [ZMod.val_natCast_of_lt hw] using this
  have hmz : (v : ℤ) % q = (w : ℤ) := by exact_mod_cast hm
  rw [symmRes, hmz, if_pos (by exact_mod_cast hh)]

lemma many_c (N q : ℕ) (hq : 0 < q) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → Fin q), Function.Injective c ∧
      q ≤ 12 * Fintype.card ι ∧
      ∀ i, |(symmRes (q : ℤ) ((c i : ℕ) * (N : ℤ)) : ℝ)| ≤ (q : ℝ) / 12 := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let g := Nat.gcd N q
  let h := q / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right N hq
  have hgh : g * h = q := Nat.mul_div_cancel' (Nat.gcd_dvd_right N q)
  have hh : 0 < h := by nlinarith
  let ι := Fin (h / 12 + 1) × Fin g
  let f : ι → ZMod q := fun i => (Nat.gcdA N q : ℤ) * (i.1 : ℕ) + (h : ZMod q) * (i.2 : ℕ)
  let c : ι → Fin q := fun i => ⟨(f i).val, ZMod.val_lt _⟩
  have hik (i : ι) : (i.1 : ℕ) < h := by have := i.1.isLt; omega
  have him (i : ι) : (i.2 : ℕ) < g := i.2.isLt
  have hmul (i : ι) : (N : ZMod q) * f i = ((g * (i.1 : ℕ) : ℕ) : ZMod q) := by
    dsimp [f]
    rw [mul_add, ← mul_assoc, bezout, ← mul_assoc, kernel_step, zero_mul, add_zero]
    simp [Nat.cast_mul, g]
  have hi : Function.Injective f := by
    intro i j hij
    have hk := congrArg (fun x : ZMod q => (N : ZMod q) * x) hij
    rw [hmul, hmul] at hk
    have hk' := congrArg ZMod.val hk
    rw [ZMod.val_natCast_of_lt (by nlinarith [hik i]), ZMod.val_natCast_of_lt (by nlinarith [hik j])] at hk'
    have hki : i.1 = j.1 := Fin.ext (by nlinarith)
    have hm : ((h * (i.2 : ℕ) : ℕ) : ZMod q) = (h * (j.2 : ℕ) : ℕ) := by
      dsimp [f] at hij
      rw [hki] at hij
      simpa only [Nat.cast_mul] using add_left_cancel hij
    have hm' := congrArg ZMod.val hm
    rw [ZMod.val_natCast_of_lt (by nlinarith [him i]), ZMod.val_natCast_of_lt (by nlinarith [him j])] at hm'
    exact Prod.ext hki (Fin.ext (by nlinarith))
  refine ⟨ι, inferInstance, c, ?_, ?_, ?_⟩
  · intro i j hij
    apply hi
    have hv := congrArg Fin.val hij
    have hcast := congrArg (fun x : ℕ => (x : ZMod q)) hv
    simpa [c] using hcast
  · simp only [ι, Fintype.card_prod, Fintype.card_fin]
    have hdiv : h ≤ 12 * (h / 12 + 1) := by omega
    nlinarith
  · intro i
    have h12 : 12 * (i.1 : ℕ) ≤ h := by have := i.1.isLt; omega
    have hkq : g * (i.1 : ℕ) < q := by nlinarith [hik i]
    have hhalf : 2 * (g * (i.1 : ℕ)) ≤ q := by nlinarith
    have hv : (((c i : ℕ) * N : ℕ) : ZMod q) = (g * (i.1 : ℕ) : ℕ) := by
      simpa [c, mul_comm] using hmul i
    have hres := simple_residue q ((c i : ℕ) * N) (g * (i.1 : ℕ)) hq hkq hhalf hv
    have hres' : symmRes (q : ℤ) ((c i : ℕ) * (N : ℤ)) = (g * (i.1 : ℕ) : ℕ) := by simpa using hres
    rw [hres', Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    have hnat : 12 * (g * (i.1 : ℕ)) ≤ q := by nlinarith
    have hreal : (12 : ℝ) * (g * (i.1 : ℕ) : ℕ) ≤ q := by exact_mod_cast hnat
    linarith

open Classical in
lemma good_pairs_count (p q r : ℕ) (hp : 1 ≤ p) (hq : 0 < q) :
    q ≤ 12 * (Finset.univ.filter (fun cd : Fin q × Fin q => IsGood p q r cd.1 cd.2)).card := by
  classical
  obtain ⟨ι, inst, c, hi, hcard, hc⟩ := many_c (p - 1) q hq
  letI := inst
  have hd (i : ι) : ∃ d : Fin q, IsGood p q r (c i) d := by
    apply good_d p q r hq (c i)
    simpa [Nat.cast_sub hp] using hc i
  choose d hd using hd
  let f : ι → Fin q × Fin q := fun i => (c i, d i)
  have hf : Function.Injective f := by
    intro i j he
    exact hi (congrArg Prod.fst he)
  have hle := Finset.card_le_card_of_injOn f
    (s := Finset.univ) (t := Finset.univ.filter (fun cd : Fin q × Fin q => IsGood p q r cd.1 cd.2))
    (by intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd i⟩)
    (by intro i _ j _ he; exact hf he)
  simp only [Finset.card_univ] at hle
  omega
end AShorLogCount

open ShorAlgorithms.DiscreteLog
namespace AShorLogLower
open Classical in
lemma total_lower (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r q l : ℕ) (hq : q = 2^l) (hpq : p < q) (hqp : q < 2*p) :
    (1 : ℝ) / 480 ≤ ∑ c : Fin q, ∑ d : Fin q,
      if IsGood p q r c d then ∑ y : (ZMod p)ˣ, outcomeProb p g (g^r) q c d y else 0 := by
  classical
  let s := Finset.univ.filter (fun cd : Fin q × Fin q => IsGood p q r cd.1 cd.2)
  have hq0 : 0 < q := lt_trans hp.out.pos hpq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hcard : (q : ℝ) ≤ 12 * (s.card : ℝ) := by
    exact_mod_cast AShorLogCount.good_pairs_count p q r hp.out.one_le hq0
  have hsum : (s.card : ℝ) * (1 / (40 * (q : ℝ))) ≤
      ∑ cd ∈ s, ∑ y : (ZMod p)ˣ, outcomeProb p g (g^r) q cd.1 cd.2 y := by
    calc _ = ∑ cd ∈ s, 1 / (40 * (q : ℝ)) := by simp
         _ ≤ _ := Finset.sum_le_sum (fun cd hcd =>
           le_trans (numeric_bound p q l hq hpq hqp)
             (good_pair_sum p g hg r q hpq cd.1 cd.2 (Finset.mem_filter.mp hcd).2))
  have hnum : (1 : ℝ) / 480 ≤ (s.card : ℝ) * (1 / (40 * (q : ℝ))) := by
    rw [mul_one_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 40 * q)).mpr
    nlinarith
  apply le_trans hnum
  simpa only [s, Finset.sum_filter, Fintype.sum_prod_type] using hsum
end AShorLogLower
open Classical in
theorem solution (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r : ℕ) (hr : r < p - 1) (q l : ℕ) (hq : q = 2 ^ l) (hpq : p < q) (hqp : q < 2 * p) :
    (1 : ℝ) / 480 ≤ ∑ c : Fin q, ∑ d : Fin q,
      if IsGood p q r c d then ∑ y : (ZMod p)ˣ, outcomeProb p g (g ^ r) q c d y else 0  := by
  exact AShorLogLower.total_lower p g hg r q l hq hpq hqp
