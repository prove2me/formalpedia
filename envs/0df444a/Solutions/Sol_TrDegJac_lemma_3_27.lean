-- Prove2me | solution 1 for TrDegJac.lemma_3_27
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-13T02:09:59.857611+00:00
-- url     : https://prove2.me/submissions/0623665c-741a-45a0-b759-c0f10c65e0b6

import Mathlib
set_option autoImplicit false

theorem solution (n d' a b : ℕ) (hab : b < a) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, b * (n + B + d').choose n < a * (n + B).choose n := by
  -- identity: C(n+B+d, n) * ∏_{j<d} (B+j+1) = C(n+B, n) * ∏_{j<d} (n+B+j+1)
  have hid : ∀ B d : ℕ, (n + B + d).choose n * ∏ j ∈ Finset.range d, (B + j + 1) =
      (n + B).choose n * ∏ j ∈ Finset.range d, (n + B + j + 1) := by
    intro B d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      have h := Nat.choose_mul_succ_eq (n + B + d) n
      have h' : n + B + d + 1 - n = B + d + 1 := by omega
      rw [h'] at h
      calc (n + B + (d + 1)).choose n * ((∏ j ∈ Finset.range d, (B + j + 1)) * (B + d + 1))
          = ((n + B + d + 1).choose n * (B + d + 1)) * ∏ j ∈ Finset.range d, (B + j + 1) := by
            rw [← add_assoc]; ring
        _ = ((n + B + d).choose n * ∏ j ∈ Finset.range d, (B + j + 1)) * (n + B + d + 1) := by
            rw [← h]; ring
        _ = (n + B).choose n * ((∏ j ∈ Finset.range d, (n + B + j + 1)) * (n + B + d + 1)) := by
            rw [ih]; ring
  -- the ratio of the two products tends to `1`
  have hlim : Filter.Tendsto
      (fun B : ℕ => (b : ℝ) * ∏ j ∈ Finset.range d', (1 + (n : ℝ) / ((B : ℝ) + j + 1)))
      Filter.atTop (nhds ((b : ℝ) * ∏ j ∈ Finset.range d', (1 : ℝ))) := by
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetProd
    intro j _
    have h0 : Filter.Tendsto (fun B : ℕ => (n : ℝ) / ((B : ℝ) + j + 1)) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      apply Filter.tendsto_atTop_add_const_right
      apply Filter.tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h0
  simp only [Finset.prod_const_one, mul_one] at hlim
  have hev := hlim.eventually_lt_const (show (b : ℝ) < a by exact_mod_cast hab)
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨B₀, fun B hB => ?_⟩
  have h1 := hB₀ B hB
  have hP1 : (0 : ℝ) < ∏ j ∈ Finset.range d', ((B : ℝ) + j + 1) :=
    Finset.prod_pos fun j _ => by positivity
  have hfac : ∏ j ∈ Finset.range d', (1 + (n : ℝ) / ((B : ℝ) + j + 1)) =
      (∏ j ∈ Finset.range d', ((n : ℝ) + B + j + 1)) /
        ∏ j ∈ Finset.range d', ((B : ℝ) + j + 1) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have : (0 : ℝ) < (B : ℝ) + j + 1 := by positivity
    field_simp
    ring
  rw [hfac, ← mul_div_assoc, div_lt_iff₀ hP1] at h1
  have h2 : b * ∏ j ∈ Finset.range d', (n + B + j + 1) <
      a * ∏ j ∈ Finset.range d', (B + j + 1) := by
    have : ((b * ∏ j ∈ Finset.range d', (n + B + j + 1) : ℕ) : ℝ) <
        ((a * ∏ j ∈ Finset.range d', (B + j + 1) : ℕ) : ℝ) := by
      push_cast
      exact h1
    exact_mod_cast this
  have hc : 0 < (n + B).choose n := Nat.choose_pos (by omega)
  have hP : 0 < ∏ j ∈ Finset.range d', (B + j + 1) := Finset.prod_pos fun j _ => by omega
  have h3 : b * (n + B + d').choose n * ∏ j ∈ Finset.range d', (B + j + 1) <
      a * (n + B).choose n * ∏ j ∈ Finset.range d', (B + j + 1) := by
    calc b * (n + B + d').choose n * ∏ j ∈ Finset.range d', (B + j + 1)
        = (n + B).choose n * (b * ∏ j ∈ Finset.range d', (n + B + j + 1)) := by
          rw [mul_assoc, hid B d']; ring
      _ < (n + B).choose n * (a * ∏ j ∈ Finset.range d', (B + j + 1)) :=
          Nat.mul_lt_mul_of_pos_left h2 hc
      _ = a * (n + B).choose n * ∏ j ∈ Finset.range d', (B + j + 1) := by ring
  exact lt_of_mul_lt_mul_right h3 (Nat.zero_le _)
