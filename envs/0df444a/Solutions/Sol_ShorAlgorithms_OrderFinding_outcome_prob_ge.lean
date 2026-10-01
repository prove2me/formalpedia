-- Prove2me | solution 1 for ShorAlgorithms.OrderFinding.outcome_prob_ge
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:26:30.537809+00:00
-- url     : https://prove2.me/submissions/cabc926c-e2d5-4465-8cd5-6f475e67b9bd

import Mathlib
import Definitions.Def_ShorAlgorithms_OrderFinding_outcomeProb
open ShorAlgorithms.OrderFinding ShorAlgorithms.Shared
namespace AShorOrder
lemma sqrt_inv_sq (q : ℕ) : ((Real.sqrt q : ℝ) : ℂ)⁻¹ * ((Real.sqrt q : ℝ) : ℂ)⁻¹ = (q : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg q)]
  rfl

lemma amplitude (n x q : ℕ) (c : Fin q) (y : ZMod n) :
    finalState n x q (c, y) = (1 / (q : ℂ)) * ∑ a ∈ (Finset.univ : Finset (Fin q)).filter
      (fun a : Fin q => (x : ZMod n) ^ (a : ℕ) = y),
        Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ)) := by
  classical
  simp only [finalState, preFourierState, fourierMatrix, Finset.sum_filter, Finset.mul_sum, one_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (x : ZMod n) ^ (a : ℕ) = y
  · simp only [h, if_true, ← mul_assoc, sqrt_inv_sq]
  · simp [h]

lemma mod_sum {q r k : ℕ} (hr : 0 < r) (hk : k < r) (hkq : k < q) (F : ℕ → ℂ) :
    (∑ a ∈ (Finset.univ : Finset (Fin q)).filter (fun a : Fin q => (a : ℕ) % r = k), F (a : ℕ)) =
      ∑ b ∈ Finset.range ((q - k - 1) / r + 1), F (b * r + k) := by
  classical
  apply Finset.sum_bij (fun (a : Fin q) _ => (a : ℕ) / r)
  · intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    have he : (a : ℕ) / r * r + k = a := by
      simpa [ha', Nat.mul_comm] using Nat.div_add_mod (a : ℕ) r
    simp only [Finset.mem_range, Nat.lt_add_one_iff]
    apply (Nat.le_div_iff_mul_le hr).mpr
    omega
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    apply Fin.ext
    have ea := Nat.mod_add_div (a : ℕ) r
    have eb := Nat.mod_add_div (b : ℕ) r
    rw [ha'] at ea
    rw [hb', ← hab] at eb
    omega
  · intro b hb
    have hb' : b * r ≤ q - k - 1 := (Nat.le_div_iff_mul_le hr).mp (Nat.le_of_lt_succ (Finset.mem_range.mp hb))
    have hbound : b * r + k < q := by omega
    refine ⟨⟨b * r + k, hbound⟩, ?_, ?_⟩
    · simp [Nat.add_mod, Nat.mod_eq_of_lt hk]
    · change (b * r + k) / r = b
      rw [Nat.mul_comm b r, Nat.mul_add_div hr, Nat.div_eq_of_lt hk, add_zero]
  · intro a ha
    congr 1
    have ha' := (Finset.mem_filter.mp ha).2
    simpa [ha', Nat.mul_comm] using (Nat.div_add_mod (a : ℕ) r).symm

lemma prob_formula (n x q l : ℕ) (hx : Nat.Coprime x n)
    (hq : q = 2 ^ l) (hnq : n ^ 2 ≤ q) (hq2 : q < 2 * n ^ 2)
    (c : Fin q) (k : ℕ) (hk : k < orderOf (x : ZMod n)) :
    outcomeProb n x q c ((x : ZMod n) ^ k) =
        ‖(1 / (q : ℂ)) * ∑ a ∈ (Finset.univ : Finset (Fin q)).filter
            (fun a : Fin q => (x : ZMod n) ^ (a : ℕ) = (x : ZMod n) ^ k),
          Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ))‖ ^ 2 ∧
    outcomeProb n x q c ((x : ZMod n) ^ k) =
        ‖(1 / (q : ℂ)) * ∑ b ∈ Finset.range ((q - k - 1) / orderOf (x : ZMod n) + 1),
          Complex.exp (2 * Real.pi * Complex.I *
            (((b * orderOf (x : ZMod n) + k : ℕ)) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ))‖ ^ 2 := by
  classical
  have hn0 : n ≠ 0 := by intro he; subst n; simp at hq2
  haveI : NeZero n := ⟨hn0⟩
  have hxfin : IsOfFinOrder (x : ZMod n) := ((ZMod.isUnit_iff_coprime x n).mpr hx).isOfFinOrder
  have hrn : orderOf (x : ZMod n) ≤ n := by simpa using (orderOf_le_card_univ (x := (x : ZMod n)))
  have hkq : k < q := lt_of_lt_of_le hk (hrn.trans ((Nat.le_self_pow (by norm_num : 2 ≠ 0) n).trans hnq))
  have hfilter : (Finset.univ : Finset (Fin q)).filter (fun a : Fin q => (x : ZMod n) ^ (a : ℕ) = (x : ZMod n) ^ k) =
      Finset.univ.filter (fun a : Fin q => (a : ℕ) % orderOf (x : ZMod n) = k) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hxfin.pow_inj_mod, Nat.mod_eq_of_lt hk]
  rw [outcomeProb, amplitude]
  refine ⟨rfl, ?_⟩
  rw [hfilter, mod_sum hxfin.orderOf_pos hk hkq (fun a => Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (c : ℕ) / (q : ℂ)))]

end AShorOrder

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

namespace AShorLower
lemma outcome_point (n x q l : ℕ) (hn : 1000 ≤ n) (hx : Nat.Coprime x n)
    (hq : q = 2 ^ l) (hnq : n ^ 2 ≤ q) (hq2 : q < 2 * n ^ 2)
    (c : Fin q) (k : ℕ) (hk : k < orderOf (x : ZMod n)) (d : ℤ)
    (hd : -((orderOf (x : ZMod n) : ℝ) / 2) ≤
      (orderOf (x : ZMod n) : ℝ) * ((c : ℕ) : ℝ) - (d : ℝ) * (q : ℝ) ∧
      (orderOf (x : ZMod n) : ℝ) * ((c : ℕ) : ℝ) - (d : ℝ) * (q : ℝ) ≤
      (orderOf (x : ZMod n) : ℝ) / 2) :
    1 / (3 * (orderOf (x : ZMod n) : ℝ) ^ 2) ≤
      ShorAlgorithms.OrderFinding.outcomeProb n x q c ((x : ZMod n) ^ k) := by
  haveI : NeZero n := ⟨by omega⟩
  let r := orderOf (x : ZMod n)
  have hrf : IsOfFinOrder (x : ZMod n) := ((ZMod.isUnit_iff_coprime x n).mpr hx).isOfFinOrder
  have hr : 0 < r := hrf.orderOf_pos
  have hrn : r ≤ n := by simpa [r] using (orderOf_le_card_univ (x := (x : ZMod n)))
  have h1000 := enough_samples hn hrn hnq
  have hqr : r ≤ q := by omega
  have hq0 : 0 < q := hr.trans_le hqr
  have hkq : k < q := hk.trans_le hqr
  have hR : (0 : ℝ) < r := by exact_mod_cast hr
  have hQ : (0 : ℝ) < q := by exact_mod_cast hq0
  let M := (q - k - 1) / r + 1
  let θ : ℝ := 2 * Real.pi * ((r : ℝ) * (c : ℕ) - (d : ℝ) * q) / q
  have hθ : |θ| ≤ Real.pi * r / q := by
    have he : |(r : ℝ) * (c : ℕ) - (d : ℝ) * q| ≤ (r : ℝ) / 2 := abs_le.mpr hd
    dsimp [θ]
    rw [abs_div, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos), abs_of_pos hQ]
    calc (2 * Real.pi) * |(r : ℝ) * (c : ℕ) - (d : ℝ) * q| / q
        ≤ (2 * Real.pi) * ((r : ℝ) / 2) / q := by gcongr
      _ = _ := by ring
  obtain ⟨hMl, hMu⟩ := series_bounds hr hk hkq
  have hL := analytic_bound M θ (r : ℝ) (q : ℝ) hR (by exact_mod_cast h1000) hMl hMu hθ
  rw [← shifted_norm q r k c M d hq0] at hL
  let S : ℂ := ∑ b ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I *
      (((b * r + k : ℕ)) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ))
  have hz : (289 / 500 : ℝ) / r ≤ (1 / (q : ℝ)) * ‖S‖ := by
    have h := mul_le_mul_of_nonneg_left hL (show 0 ≤ (1 : ℝ) / q by positivity)
    have he : (1 / (q : ℝ)) * ((289 / 500 : ℝ) * q / r) = (289 / 500 : ℝ) / r := by
      field_simp
    rw [he] at h
    exact h
  rw [(AShorOrder.prob_formula n x q l hx hq hnq hq2 c k hk).2]
  change 1 / (3 * (r : ℝ) ^ 2) ≤ ‖(1 / (q : ℂ)) * S‖ ^ 2
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  calc
    1 / (3 * (r : ℝ) ^ 2) ≤ (289 / 500 : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
      have h := div_le_div_of_nonneg_right (show (1 / 3 : ℝ) ≤ (289 / 500 : ℝ) ^ 2 by norm_num) (sq_nonneg (r : ℝ))
      simpa only [div_div] using h
    _ = ((289 / 500 : ℝ) / r) ^ 2 := (div_pow _ _ _).symm
    _ ≤ ((1 / (q : ℝ)) * ‖S‖) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (by positivity : 0 ≤ (289 / 500 : ℝ) / r) hz
end AShorLower

theorem solution : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : ℕ, Nat.Coprime x n →
    ∀ q l : ℕ, q = 2 ^ l → n ^ 2 ≤ q → q < 2 * n ^ 2 →
    ∀ c : Fin q, ∀ k : ℕ, k < orderOf (x : ZMod n) →
    (∃ d : ℤ,
        -((orderOf (x : ZMod n) : ℝ) / 2) ≤
          (orderOf (x : ZMod n) : ℝ) * ((c : ℕ) : ℝ) - (d : ℝ) * (q : ℝ) ∧
        (orderOf (x : ZMod n) : ℝ) * ((c : ℕ) : ℝ) - (d : ℝ) * (q : ℝ) ≤
          (orderOf (x : ZMod n) : ℝ) / 2) →
    1 / (3 * (orderOf (x : ZMod n) : ℝ) ^ 2) ≤ outcomeProb n x q c ((x : ZMod n) ^ k)  := by
  refine ⟨1000, ?_⟩
  intro n hn x hx q l hq hnq hq2 c k hk hd
  obtain ⟨d, hd⟩ := hd
  exact AShorLower.outcome_point n x q l hn hx hq hnq hq2 c k hk d hd
