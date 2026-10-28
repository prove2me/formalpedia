-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P54.average_resource_cost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:12:08.084433+00:00
-- url     : https://prove2.me/submissions/2f1b2940-a6d8-4aec-9721-6166339e39f7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

noncomputable section
open QAlgorithms.Papers.Independent.Information100.P54
open scoped ENNReal

namespace ARC54

def ψ (u : ℝ) : ℝ := u * Real.log u

theorem psi_zero : ψ 0 = 0 := by simp [ψ]

theorem psi_tangent {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    ψ a + (Real.log a + 1) * (u - a) ≤ ψ u := by
  unfold ψ
  rcases hu.lt_or_eq with hu | hu
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hu ha)
    rw [Real.log_div hu.ne' ha.ne', inv_div] at h
    have h2 : u * (1 - a / u) ≤ u * (Real.log u - Real.log a) := mul_le_mul_of_nonneg_left h hu.le
    rw [mul_sub, mul_div_cancel₀ _ hu.ne', mul_one] at h2
    nlinarith
  · subst hu; simp; nlinarith [ha]

/-- F(t) = ψ(t+s) - ψ(t). -/
def F (s t : ℝ) : ℝ := ψ (t + s) - ψ t

theorem step (s : ℝ) (hs : 1 ≤ s) (t : ℕ) :
    Real.log (s + t) - Real.log (t + 1) ≤ F s (t + 1) - F s t := by
  unfold F
  have h1 := psi_tangent (a := (t:ℝ) + s) (u := (t:ℝ) + 1 + s) (by positivity) (by positivity)
  have h2 := psi_tangent (a := (t:ℝ) + 1) (u := (t:ℝ)) (by positivity) (by positivity)
  rw [add_comm s (t:ℝ)]
  nlinarith

def D (s m : ℕ) : ℝ := (sectorDimension s m : ℝ)

theorem D_pos (s m : ℕ) (hs : 1 ≤ s) : 0 < D s m := by
  unfold D sectorDimension
  exact_mod_cast Nat.choose_pos (by omega)

theorem D_succ (s t : ℕ) (hs : 1 ≤ s) : D s (t + 1) * (t + 1) = D s t * (s + t) := by
  unfold D sectorDimension
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have := Nat.add_one_mul_choose_eq (s' + t) t
  rw [show s' + 1 + (t + 1) - 1 = s' + t + 1 by omega, show s' + 1 + t - 1 = s' + t by omega]
  have h : ((s' + t + 1).choose (t + 1) : ℝ) * ((t:ℝ) + 1) = ((s' + t).choose t : ℝ) * ((s' + t + 1 : ℕ) : ℝ) := by
    have h' : (s' + t + 1).choose (t + 1) * (t + 1) = (s' + t).choose t * (s' + t + 1) := by
      rw [mul_comm ((s' + t).choose t)]; exact this.symm
    exact_mod_cast h'
  rw [h]; push_cast; ring

theorem logD_step (s t : ℕ) (hs : 1 ≤ s) :
    Real.log (D s (t + 1)) - Real.log (D s t) = Real.log (s + t) - Real.log (t + 1) := by
  have h := D_succ s t hs
  have hp := D_pos s t hs
  have hp' := D_pos s (t+1) hs
  have := congrArg Real.log h
  rw [Real.log_mul hp'.ne' (by positivity), Real.log_mul hp.ne' (by positivity)] at this
  linarith

theorem logD_mono (s : ℕ) (hs : 1 ≤ s) {l m : ℕ} (hlm : l ≤ m) :
    Real.log (D s l) ≤ Real.log (D s m) := by
  induction m, hlm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    have := logD_step s m hs
    have hs' : (1:ℝ) ≤ s := by exact_mod_cast hs
    have h2 : Real.log (m + 1) ≤ Real.log (s + m) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith

theorem logD_F (s : ℕ) (hs : 1 ≤ s) {l m : ℕ} (hlm : l ≤ m) :
    Real.log (D s m) - Real.log (D s l) ≤ F s m - F s l := by
  induction m, hlm using Nat.le_induction with
  | base => simp
  | succ m _ ih =>
    have := logD_step s m hs
    have h2 := step (s:ℝ) (by exact_mod_cast hs) m
    push_cast at h2 ⊢
    linarith

/-- binomial mass with success prob q (lost photons). -/
def b (m : ℕ) (q : ℝ) (l : ℕ) : ℝ := (m.choose l : ℝ) * q ^ l * (1 - q) ^ (m - l)

theorem b_pos {m : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {l : ℕ} (hl : l ≤ m) : 0 < b m q l := by
  unfold b
  have : (0:ℝ) < m.choose l := by exact_mod_cast Nat.choose_pos hl
  have : 0 < 1 - q := by linarith
  positivity

theorem b_sum (m : ℕ) (q : ℝ) : ∑ l ∈ Finset.range (m + 1), b m q l = 1 := by
  have := (add_pow q (1 - q) m).symm
  rw [show q + (1 - q) = 1 by ring, one_pow] at this
  rw [← this]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold b; ring

theorem b_mean (m : ℕ) (q : ℝ) : ∑ l ∈ Finset.range (m + 1), b m q l * l = m * q := by
  cases m with
  | zero => simp [b]
  | succ m =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, add_zero]
    have h : ∀ l ∈ Finset.range (m + 1), b (m + 1) q (l + 1) * ((l + 1 : ℕ) : ℝ) =
        (m + 1 : ℝ) * q * b m q l := by
      intro l hl
      have hl' : l ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      unfold b
      have hc : ((m + 1).choose (l + 1) : ℝ) * ((l + 1 : ℕ) : ℝ) = (m + 1 : ℝ) * (m.choose l) := by
        have := Nat.add_one_mul_choose_eq m l
        exact_mod_cast this.symm
      rw [show m + 1 - (l + 1) = m - l by omega, pow_succ]
      linear_combination (q ^ l * q * (1 - q) ^ (m - l)) * hc
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum, b_sum]; push_cast; ring

/-- log C(m,l) ≤ ψ m - ψ l - ψ (m-l). -/
theorem logchoose_le (m l : ℕ) (hl : l ≤ m) :
    Real.log (m.choose l) ≤ ψ m - ψ l - ψ ((m:ℝ) - l) := by
  unfold ψ
  rcases Nat.eq_zero_or_pos l with h0 | hlpos
  · subst h0; simp
  rcases hl.lt_or_eq with hlt | heq
  · have hm : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    set a : ℝ := l / m
    have ha : 0 < a := by positivity
    have ha1 : 0 < 1 - a := by
      have : (l:ℝ) < m := by exact_mod_cast hlt
      simp only [a]; rw [sub_pos, div_lt_one hm]; exact this
    have key : (m.choose l : ℝ) * a ^ l * (1 - a) ^ (m - l) ≤ 1 := by
      have hsum := add_pow a (1 - a) m
      rw [show a + (1 - a) = 1 by ring, one_pow] at hsum
      have := Finset.single_le_sum (f := fun k => a ^ k * (1 - a) ^ (m - k) * (m.choose k : ℝ))
        (fun k _ => by positivity) (Finset.mem_range.mpr (by omega : l < m + 1))
      calc (m.choose l : ℝ) * a ^ l * (1 - a) ^ (m - l) = a ^ l * (1 - a) ^ (m - l) * (m.choose l : ℝ) := by ring
        _ ≤ _ := this
        _ = 1 := hsum.symm
    have hc : (0:ℝ) < m.choose l := by exact_mod_cast Nat.choose_pos hl
    have hlog := Real.log_le_log (by positivity) key
    rw [Real.log_one, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
    have e1 : Real.log a = Real.log l - Real.log m := Real.log_div (by positivity) hm.ne'
    have e2 : 1 - a = ((m:ℝ) - l) / m := by simp only [a]; field_simp
    have hlt' : (l:ℝ) < m := by exact_mod_cast hlt
    have hml : (0:ℝ) < (m:ℝ) - l := by linarith
    have e3 : Real.log (1 - a) = Real.log ((m:ℝ) - l) - Real.log m := by
      rw [e2, Real.log_div hml.ne' hm.ne']
    rw [e1, e3] at hlog
    have : ((m - l : ℕ) : ℝ) = (m:ℝ) - l := by push_cast [hl]; ring
    rw [this] at hlog
    nlinarith
  · subst heq; simp

theorem b_zero (q : ℝ) : b 0 q 0 = 1 := by simp [b]

theorem cast_sub_le {m l : ℕ} (h : l ≤ m) : ((m - l : ℕ) : ℝ) = (m:ℝ) - l := by push_cast [h]; ring

theorem log_b {m : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {l : ℕ} (hl : l ≤ m) :
    Real.log (b m q l) = Real.log (m.choose l) + l * Real.log q + ((m:ℝ) - l) * Real.log (1 - q) := by
  unfold b
  have : (0:ℝ) < m.choose l := by exact_mod_cast Nat.choose_pos hl
  have : 0 < 1 - q := by linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, cast_sub_le hl]

theorem sum_tangent (m : ℕ) (q : ℝ) (f : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hf : ∀ l ∈ Finset.range (m + 1), 0 ≤ f l) (hb : ∀ l ∈ Finset.range (m + 1), 0 ≤ b m q l)
    (hmean : ∑ l ∈ Finset.range (m + 1), b m q l * f l = a) :
    ψ a ≤ ∑ l ∈ Finset.range (m + 1), b m q l * ψ (f l) := by
  have h : ∀ l ∈ Finset.range (m + 1), b m q l * (ψ a + (Real.log a + 1) * (f l - a)) ≤
      b m q l * ψ (f l) := fun l hl => mul_le_mul_of_nonneg_left (psi_tangent ha (hf l hl)) (hb l hl)
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum h)
  have e : ∀ l ∈ Finset.range (m + 1), b m q l * (ψ a + (Real.log a + 1) * (f l - a)) =
      b m q l * (ψ a - (Real.log a + 1) * a) + (Real.log a + 1) * (b m q l * f l) := by
    intro l _; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.sum_mul, b_sum, ← Finset.mul_sum, hmean]
  ring

def H (m : ℕ) (q : ℝ) : ℝ := ∑ l ∈ Finset.range (m + 1), -(b m q l * Real.log (b m q l))

theorem part1_nats (s : ℕ) (hs : 1 ≤ s) (m : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Real.log (D s m) - ∑ l ∈ Finset.range (m + 1), b m q l * Real.log (D s l) ≤
      F s m - F s (q * m) + H m q := by
  have hb : ∀ l ∈ Finset.range (m + 1), 0 ≤ b m q l := fun l hl =>
    (b_pos hq0 hq1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))).le
  have hs' : (1:ℝ) ≤ s := by exact_mod_cast hs
  -- step 1
  have h1 : Real.log (D s m) - ∑ l ∈ Finset.range (m + 1), b m q l * Real.log (D s l) ≤
      F s m - ∑ l ∈ Finset.range (m + 1), b m q l * F s l := by
    have e1 : Real.log (D s m) - ∑ l ∈ Finset.range (m + 1), b m q l * Real.log (D s l) =
        ∑ l ∈ Finset.range (m + 1), b m q l * (Real.log (D s m) - Real.log (D s l)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, b_sum, one_mul]
    have e2 : F s m - ∑ l ∈ Finset.range (m + 1), b m q l * F s l =
        ∑ l ∈ Finset.range (m + 1), b m q l * (F s m - F s l) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, b_sum, one_mul]
    rw [e1, e2]
    exact Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left
      (logD_F s hs (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))) (hb l hl)
  -- step 2
  have h2 : ψ (q * m + s) ≤ ∑ l ∈ Finset.range (m + 1), b m q l * ψ ((l:ℝ) + s) := by
    apply sum_tangent m q (fun l => (l:ℝ) + s) _ (by positivity) (fun l _ => by positivity) hb
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, b_sum, one_mul, b_mean]; ring
  -- step 3
  have h3 : ∑ l ∈ Finset.range (m + 1), b m q l * ψ (l:ℝ) ≤ ψ (q * m) + H m q := by
    have key : ∑ l ∈ Finset.range (m + 1), b m q l * (ψ (l:ℝ) + Real.log (b m q l)) ≤ ψ (q * m) := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0; simp [b_zero, psi_zero]
      have hm : (0:ℝ) < m := by exact_mod_cast hmpos
      have hT : ∀ l ∈ Finset.range (m + 1), b m q l * (ψ (l:ℝ) + Real.log (b m q l)) ≤
          b m q l * (ψ m - ψ ((m:ℝ) - l) + l * Real.log q + ((m:ℝ) - l) * Real.log (1 - q)) := by
        intro l hl
        have hl' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        apply mul_le_mul_of_nonneg_left _ (hb l hl)
        rw [log_b hq0 hq1 hl']
        have := logchoose_le m l hl'
        linarith
      have hS : ψ ((m:ℝ) - q * m) ≤ ∑ l ∈ Finset.range (m + 1), b m q l * ψ ((m:ℝ) - l) := by
        apply sum_tangent m q (fun l => (m:ℝ) - l) _ (by nlinarith) (fun l hl => by
          have hl' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          have : (l:ℝ) ≤ m := by exact_mod_cast hl'
          show (0:ℝ) ≤ (m:ℝ) - l; linarith) hb
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, b_sum, one_mul, b_mean]
        ring
      have e : ∑ l ∈ Finset.range (m + 1),
          b m q l * (ψ m - ψ ((m:ℝ) - l) + l * Real.log q + ((m:ℝ) - l) * Real.log (1 - q)) =
          ψ m - ∑ l ∈ Finset.range (m + 1), b m q l * ψ ((m:ℝ) - l) + (q * m) * Real.log q +
            ((m:ℝ) - q * m) * Real.log (1 - q) := by
        have e' : ∀ l ∈ Finset.range (m + 1),
            b m q l * (ψ m - ψ ((m:ℝ) - l) + l * Real.log q + ((m:ℝ) - l) * Real.log (1 - q)) =
            b m q l * (ψ m + m * Real.log (1 - q)) - b m q l * ψ ((m:ℝ) - l) +
              (b m q l * l) * (Real.log q - Real.log (1 - q)) := by
          intro l _; ring
        rw [Finset.sum_congr rfl e', Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_mul, b_sum, ← Finset.sum_mul, b_mean]
        ring
      have hfin : ψ m - ψ ((m:ℝ) - q * m) + (q * m) * Real.log q + ((m:ℝ) - q * m) * Real.log (1 - q)
          = ψ (q * m) := by
        unfold ψ
        rw [show (m:ℝ) - q * m = m * (1 - q) by ring, Real.log_mul hm.ne' (by linarith),
          Real.log_mul hq0.ne' hm.ne']
        ring
      linarith [Finset.sum_le_sum hT]
    have e : ∑ l ∈ Finset.range (m + 1), b m q l * ψ (l:ℝ) =
        ∑ l ∈ Finset.range (m + 1), b m q l * (ψ (l:ℝ) + Real.log (b m q l)) + H m q := by
      unfold H
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    linarith
  unfold F at h1 ⊢
  simp only [mul_sub, Finset.sum_sub_distrib] at h1
  linarith

theorem H_le (m : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    H m q ≤ ψ (q * m + 1) - ψ (q * m) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0; simp [H, b_zero, psi_zero, ψ]
  have hm : (0:ℝ) < m := by exact_mod_cast hmpos
  set μ := q * m with hμ
  have hμ0 : 0 < μ := by positivity
  set x := μ / (1 + μ) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
  have h1x : 1 - x = 1 / (1 + μ) := by rw [hx]; field_simp; ring
  have hb : ∀ l ∈ Finset.range (m + 1), 0 < b m q l := fun l hl =>
    b_pos hq0 hq1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))
  -- Gibbs termwise
  have hG : ∀ l ∈ Finset.range (m + 1), -(b m q l * Real.log (b m q l)) ≤
      -(b m q l * (Real.log (1 - x) + l * Real.log x)) + ((1 - x) * x ^ l - b m q l) := by
    intro l hl
    have hbl := hb l hl
    have h1x' : 0 < 1 - x := by linarith
    have hr : 0 < (1 - x) * x ^ l := by positivity
    have := Real.log_le_sub_one_of_pos (div_pos hr hbl)
    rw [Real.log_div hr.ne' hbl.ne', Real.log_mul (by linarith) (by positivity), Real.log_pow] at this
    have h2 := mul_le_mul_of_nonneg_left this hbl.le
    have h3 : b m q l * ((1 - x) * x ^ l / b m q l - 1) = (1 - x) * x ^ l - b m q l := by
      field_simp
    rw [h3] at h2
    linarith
  have hsum := Finset.sum_le_sum hG
  have hgeo : ∑ l ∈ Finset.range (m + 1), (1 - x) * x ^ l ≤ 1 := by
    rw [← Finset.mul_sum]
    have := geom_sum_mul x (m + 1)
    have hxp : 0 ≤ x ^ (m + 1) := by positivity
    nlinarith
  have e : ∑ l ∈ Finset.range (m + 1),
      (-(b m q l * (Real.log (1 - x) + l * Real.log x)) + ((1 - x) * x ^ l - b m q l)) =
      -(Real.log (1 - x) + μ * Real.log x) + (∑ l ∈ Finset.range (m + 1), (1 - x) * x ^ l - 1) := by
    have e' : ∀ l ∈ Finset.range (m + 1),
        (-(b m q l * (Real.log (1 - x) + l * Real.log x)) + ((1 - x) * x ^ l - b m q l)) =
        -(b m q l * (Real.log (1 - x) + 1)) - (b m q l * l) * Real.log x + (1 - x) * x ^ l := by
      intro l _; ring
    rw [Finset.sum_congr rfl e', Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.sum_mul, ← Finset.sum_mul, b_sum, b_mean,
      show (m:ℝ) * q = μ by rw [hμ]; ring]
    ring
  have hval : -(Real.log (1 - x) + μ * Real.log x) = ψ (μ + 1) - ψ μ := by
    unfold ψ
    rw [h1x, hx, Real.log_div (by norm_num) (by positivity), Real.log_div hμ0.ne' (by positivity),
      Real.log_one, add_comm 1 μ]
    ring
  unfold H
  linarith

theorem cost_nonneg (s : ℕ) (hs : 1 ≤ s) (m : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ Real.log (D s m) - ∑ l ∈ Finset.range (m + 1), b m q l * Real.log (D s l) := by
  have : ∑ l ∈ Finset.range (m + 1), b m q l * Real.log (D s l) ≤
      ∑ l ∈ Finset.range (m + 1), b m q l * Real.log (D s m) :=
    Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left
      (logD_mono s hs (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)))
      (b_pos hq0 hq1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))).le
  rw [← Finset.sum_mul, b_sum, one_mul] at this
  linarith

theorem hd_psi (a c t : ℝ) (h : a * t + c ≠ 0) :
    HasDerivAt (fun t => ψ (a * t + c)) (a * (Real.log (a * t + c) + 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ => a * t + c) a t := by
    simpa using ((hasDerivAt_id t).const_mul a).add_const c
  have := (Real.hasDerivAt_mul_log h).comp t h1
  unfold ψ
  exact this.congr_deriv (by ring)

theorem hd_lg (a c t : ℝ) (h : a * t + c ≠ 0) :
    HasDerivAt (fun t => a * (Real.log (a * t + c) + 1)) (a * (a * (a * t + c)⁻¹)) t := by
  have h1 : HasDerivAt (fun t : ℝ => a * t + c) a t := by
    simpa using ((hasDerivAt_id t).const_mul a).add_const c
  have := (((Real.hasDerivAt_log h).comp t h1).add_const 1).const_mul a
  exact this.congr_deriv (by ring)

def Φ (s q t : ℝ) : ℝ := ψ (1 * t + s) - ψ (1 * t + 0) - ψ (q * t + s) + ψ (q * t + 1)

theorem Φ_concave (s q : ℝ) (hs : 1 ≤ s) (hq0 : 0 < q) (hq1 : q < 1) :
    ConcaveOn ℝ (Set.Ici 0) (Φ s q) := by
  have hcont : Continuous (fun u : ℝ => ψ u) := by
    unfold ψ; exact Real.continuous_mul_log
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 0) ?_ (f' := fun t =>
      1 * (Real.log (1 * t + s) + 1) - 1 * (Real.log (1 * t + 0) + 1) - q * (Real.log (q * t + s) + 1)
        + q * (Real.log (q * t + 1) + 1))
    (f'' := fun t => 1 * (1 * (1 * t + s)⁻¹) - 1 * (1 * (1 * t + 0)⁻¹) - q * (q * (q * t + s)⁻¹)
        + q * (q * (q * t + 1)⁻¹)) ?_ ?_ ?_
  · unfold Φ; fun_prop
  · intro t ht
    rw [interior_Ici] at ht
    have ht : 0 < t := ht
    apply HasDerivAt.hasDerivWithinAt
    unfold Φ
    exact (((hd_psi 1 s t (by linarith)).sub (hd_psi 1 0 t (by linarith))).sub
      (hd_psi q s t (by positivity))).add (hd_psi q 1 t (by positivity))
  · intro t ht
    rw [interior_Ici] at ht
    have ht : 0 < t := ht
    apply HasDerivAt.hasDerivWithinAt
    exact (((hd_lg 1 s t (by linarith)).sub (hd_lg 1 0 t (by linarith))).sub
      (hd_lg q s t (by positivity))).add (hd_lg q 1 t (by positivity))
  · intro t ht
    rw [interior_Ici] at ht
    have ht : 0 < t := ht
    have e : 1 * (1 * (1 * t + s)⁻¹) - 1 * (1 * (1 * t + 0)⁻¹) - q * (q * (q * t + s)⁻¹)
        + q * (q * (q * t + 1)⁻¹) =
        -((1 - q) * s ^ 2 * (q * t + 1) + q * (t + s) * (q * t + s)) /
          (t * (t + s) * (q * t + s) * (q * t + 1)) := by
      have : t + s ≠ 0 := by linarith
      have : q * t + s ≠ 0 := by positivity
      have : q * t + 1 ≠ 0 := by positivity
      field_simp
      ring
    show _ ≤ 0
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg
    · have : 0 ≤ 1 - q := by linarith
      have : 0 ≤ (1 - q) * s ^ 2 * (q * t + 1) := by positivity
      have : 0 ≤ q * (t + s) * (q * t + s) := by positivity
      linarith
    · positivity

theorem th_def (x : ℝ) : thermalEntropy x * Real.log 2 = ψ (x + 1) - ψ x := by
  unfold thermalEntropy ψ
  field_simp

theorem th_scale (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    s * thermalEntropy (t / s) * Real.log 2 = ψ (t + s) - ψ t - ψ s := by
  rw [mul_assoc, th_def]
  unfold ψ
  rw [show t / s + 1 = (t + s) / s by field_simp, Real.log_div (by linarith) hs.ne']
  rcases ht.lt_or_eq with ht | ht
  · rw [Real.log_div ht.ne' hs.ne']; field_simp; ring
  · subst ht; simp

def Φb (eta : ℝ) (s : ℕ) (t : ℝ) : ℝ :=
  (s : ℝ) * lossRate eta (t / s) + thermalEntropy ((1 - eta) * t)

theorem Φb_eq (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) (s : ℕ) (hs : 1 ≤ s) (t : ℝ)
    (ht : 0 ≤ t) : Φb eta s t * Real.log 2 = Φ s (1 - eta) t := by
  have hs' : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  unfold Φb lossRate
  rw [show (1 - eta) * (t / s) = ((1 - eta) * t) / s by ring]
  have h1 := th_scale s t hs' ht
  have h2 := th_scale s ((1 - eta) * t) hs' (mul_nonneg (by linarith) ht)
  have h3 := th_def ((1 - eta) * t)
  unfold Φ
  simp only [one_mul, add_zero]
  linear_combination h1 - h2 + h3

theorem Φb_concave (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) (s : ℕ) (hs : 1 ≤ s) :
    ConcaveOn ℝ (Set.Ici 0) (Φb eta s) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := (Φ_concave s (1 - eta) (by exact_mod_cast hs) (by linarith) (by linarith)).smul
    (inv_nonneg.mpr hl.le)
  refine this.congr fun t ht => ?_
  simp only [smul_eq_mul]
  rw [← Φb_eq eta heta0 heta1 s hs t ht]
  field_simp

theorem Φb_cont (eta : ℝ) (s : ℕ) : Continuous (Φb eta s) := by
  have hc : Continuous (fun u : ℝ => u * Real.log u) := Real.continuous_mul_log
  unfold Φb lossRate thermalEntropy
  have h1 : Continuous (fun x : ℝ => ((x + 1) * Real.log (x + 1) - x * Real.log x) / Real.log 2) := by
    exact ((hc.comp (continuous_id.add continuous_const)).sub hc).div_const _
  exact (continuous_const.mul ((h1.comp (continuous_id.div_const _)).sub
    (h1.comp (continuous_const.mul (continuous_id.div_const _))))).add
    (h1.comp (continuous_const.mul continuous_id))

theorem Φb_zero (eta : ℝ) (s : ℕ) : Φb eta s 0 = 0 := by
  simp [Φb, lossRate, thermalEntropy]

theorem cost_eq (eta : ℝ) (s m : ℕ) :
    sectorCost eta s m * Real.log 2 =
      Real.log (D s m) - ∑ l ∈ Finset.range (m + 1), b m (1 - eta) l * Real.log (D s l) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold sectorCost
  rw [sub_mul, div_mul_cancel₀ _ hl, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold binomialMass D b
  field_simp

theorem cost_le (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) (s : ℕ) (hs : 1 ≤ s) (m : ℕ) :
    sectorCost eta s m ≤ (s : ℝ) * lossRate eta ((m : ℝ) / s) + H m (1 - eta) / Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs' : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have h := part1_nats s hs m (q := 1 - eta) (by linarith) (by linarith)
  rw [← cost_eq] at h
  have e : (s : ℝ) * lossRate eta ((m : ℝ) / s) * Real.log 2 = F s m - F s ((1 - eta) * m) := by
    unfold lossRate F
    rw [mul_sub, sub_mul, th_scale s m hs' (by positivity),
      show (1 - eta) * ((m:ℝ) / s) = ((1 - eta) * m) / s by ring,
      th_scale s ((1 - eta) * m) hs' (mul_nonneg (by linarith) (by positivity))]
    ring
  rw [← le_div_iff₀ hl] at h
  rw [← e] at h
  calc sectorCost eta s m ≤ _ := h
    _ = _ := by field_simp

theorem cost_le_Φb (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) (s : ℕ) (hs : 1 ≤ s) (m : ℕ) :
    sectorCost eta s m ≤ Φb eta s m := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := cost_le eta heta0 heta1 s hs m
  have h2 := H_le m (q := 1 - eta) (by linarith) (by linarith)
  have h3 := th_def ((1 - eta) * m)
  unfold Φb
  have : H m (1 - eta) / Real.log 2 ≤ thermalEntropy ((1 - eta) * m) := by
    rw [div_le_iff₀ hl, h3]; linarith
  linarith

theorem cost_nonneg' (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) (s : ℕ) (hs : 1 ≤ s) (m : ℕ) :
    0 ≤ sectorCost eta s m := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := cost_nonneg s hs m (q := 1 - eta) (by linarith) (by linarith)
  rw [← cost_eq] at this
  exact nonneg_of_mul_nonneg_left this hl

theorem b_le_one {m : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {l : ℕ} (hl : l ≤ m) : b m q l ≤ 1 := by
  rw [← b_sum m q]
  exact Finset.single_le_sum (f := fun l => b m q l)
    (fun k hk => (b_pos hq0 hq1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).le)
    (Finset.mem_range.mpr (by omega))

theorem part1 (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) (s : ℕ) (hs : 1 ≤ s) (m : ℕ) :
    ENNReal.ofReal (sectorCost eta s m) ≤
      ENNReal.ofReal ((s : ℝ) * lossRate eta ((m : ℝ) / s)) +
        ∑ ell ∈ Finset.range (m + 1), ENNReal.ofReal
          (-binomialMass m (1 - eta) ell * Real.log (binomialMass m (1 - eta) ell) /
            Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : ∀ ell ∈ Finset.range (m + 1), 0 ≤
      -binomialMass m (1 - eta) ell * Real.log (binomialMass m (1 - eta) ell) / Real.log 2 := by
    intro ell hell
    have hle := Nat.lt_succ_iff.mp (Finset.mem_range.mp hell)
    have h0 := (b_pos (m := m) (q := 1 - eta) (by linarith) (by linarith) hle).le
    have h1 := b_le_one (m := m) (q := 1 - eta) (by linarith) (by linarith) hle
    have := Real.mul_log_nonpos h0 h1
    apply div_nonneg _ hl.le
    show 0 ≤ -b m (1 - eta) ell * Real.log (b m (1 - eta) ell)
    linarith
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
  have h := cost_le eta heta0 heta1 s hs m
  have e : H m (1 - eta) / Real.log 2 = ∑ ell ∈ Finset.range (m + 1),
      -binomialMass m (1 - eta) ell * Real.log (binomialMass m (1 - eta) ell) / Real.log 2 := by
    unfold H; rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold binomialMass b; ring
  linarith

end ARC54

open ARC54 in
theorem ARC54.part2 (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) (s : ℕ) (hs : 1 ≤ s)
    (p : PMF ℕ) (hp : countMean p ≠ ⊤) :
    averageSectorCost eta s p ≤ ENNReal.ofReal (Φb eta s (countMean p).toReal) := by
  set μ := (countMean p).toReal
  set a : ℕ → ℝ := fun N => ∑ m ∈ Finset.range N, (p m).toReal * m with ha_def
  have ha : Filter.Tendsto a Filter.atTop (nhds μ) := by
    have h1 := ENNReal.tendsto_nat_tsum (fun m => (m:ℝ≥0∞) * p m)
    have h2 := (ENNReal.tendsto_toReal hp).comp h1
    refine h2.congr fun N => ?_
    simp only [Function.comp_apply, ha_def]
    rw [ENNReal.toReal_sum (fun m _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (PMF.apply_ne_top p m))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm]
  have hconc := Φb_concave eta heta0 heta1 s hs
  have hS : ∀ N, ∑ m ∈ Finset.range N, (p m).toReal ≤ 1 := by
    intro N
    rw [← ENNReal.toReal_sum (fun m _ => PMF.apply_ne_top p m)]
    have : ∑ m ∈ Finset.range N, p m ≤ 1 := by
      rw [← p.tsum_coe]; exact ENNReal.sum_le_tsum _
    have := ENNReal.toReal_mono ENNReal.one_ne_top this
    simpa using this
  have hpart : ∀ N, ∑ m ∈ Finset.range N, p m * ENNReal.ofReal (sectorCost eta s m) ≤
      ENNReal.ofReal (Φb eta s (a N)) := by
    intro N
    have h1 : ∑ m ∈ Finset.range N, p m * ENNReal.ofReal (sectorCost eta s m) ≤
        ∑ m ∈ Finset.range N, ENNReal.ofReal ((p m).toReal * Φb eta s m) := by
      refine Finset.sum_le_sum fun m _ => ?_
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top p m)]
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (cost_le_Φb eta heta0 heta1 s hs m)) _
    have hnn : ∀ m ∈ Finset.range N, 0 ≤ (p m).toReal * Φb eta s m := fun m _ =>
      mul_nonneg ENNReal.toReal_nonneg
        ((cost_nonneg' eta heta0 heta1 s hs m).trans (cost_le_Φb eta heta0 heta1 s hs m))
    rw [← ENNReal.ofReal_sum_of_nonneg hnn] at h1
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [ha_def, Φb_zero]
    set S := ∑ m ∈ Finset.range N, (p m).toReal
    have h0 : (0:ℕ) ∈ Finset.range N := Finset.mem_range.mpr hN
    let w : ℕ → ℝ := fun m => (p m).toReal + if m = 0 then 1 - S else 0
    have hw0 : ∀ m ∈ Finset.range N, 0 ≤ w m := by
      intro m _
      have := hS N
      have : 0 ≤ (p m).toReal := ENNReal.toReal_nonneg
      simp only [w]; split_ifs <;> linarith
    have hw1 : ∑ m ∈ Finset.range N, w m = 1 := by
      simp only [w, Finset.sum_add_distrib, Finset.sum_ite_eq', h0, if_true]; ring
    have hJ := hconc.le_map_sum (t := Finset.range N) (w := w) (p := fun m => (m:ℝ)) hw0 hw1
      (fun m _ => Set.mem_Ici.mpr (Nat.cast_nonneg m))
    simp only [smul_eq_mul] at hJ
    have e1 : ∑ m ∈ Finset.range N, w m * (m:ℝ) = a N := by
      simp only [w, add_mul, Finset.sum_add_distrib, ha_def]
      have : ∑ m ∈ Finset.range N, (if m = 0 then 1 - S else 0) * (m:ℝ) = 0 :=
        Finset.sum_eq_zero fun m _ => by split_ifs with h <;> simp [h]
      rw [this, add_zero]
    have e2 : ∑ m ∈ Finset.range N, w m * Φb eta s m =
        ∑ m ∈ Finset.range N, (p m).toReal * Φb eta s m := by
      simp only [w, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', h0,
        if_true, Nat.cast_zero, Φb_zero, mul_zero, add_zero]
    rw [e1, e2] at hJ
    exact hJ
  unfold averageSectorCost
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  have ht : Filter.Tendsto (fun K => ENNReal.ofReal (Φb eta s (a K))) Filter.atTop
      (nhds (ENNReal.ofReal (Φb eta s μ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (((Φb_cont eta s).tendsto μ).comp ha)
  refine ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨N, fun K hK => ?_⟩)
  exact (Finset.sum_le_sum_of_subset (Finset.range_mono hK)).trans (hpart K)

open ARC54 in
theorem solution (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1)
    (s : ℕ) (hs : 1 ≤ s) :
    (∀ m : ℕ, ENNReal.ofReal (sectorCost eta s m) ≤
      ENNReal.ofReal ((s : ℝ) * lossRate eta ((m : ℝ) / s)) +
        ∑ ell ∈ Finset.range (m + 1), ENNReal.ofReal
          (-binomialMass m (1 - eta) ell * Real.log (binomialMass m (1 - eta) ell) /
            Real.log 2)) ∧
    (∀ p : PMF ℕ, countMean p ≠ ⊤ →
      averageSectorCost eta s p ≤ ENNReal.ofReal
        ((s : ℝ) * lossRate eta ((countMean p).toReal / s) +
          thermalEntropy ((1 - eta) * (countMean p).toReal))) :=
  ⟨fun m => part1 eta heta0 heta1 s hs m, fun p hp => part2 eta heta0 heta1 s hs p hp⟩
