-- Prove2me | solution 1 for OddPerfectNumber.nielsen_lemma_1_4
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-08T06:59:24.514279+00:00
-- url     : https://prove2.me/submissions/c71c3df7-2afa-46f4-91a2-1e1b1e9a1d49

import Theorems.Thm_OddPerfectNumber_prod_one_sub_inv_lt_of_prod_lt

open Finset OddPerfectNumber

/-- Telescoping identity `a ∏_{i<m} ((a+1)^{2^i}+1) = (a+1)^{2^m} - 1`. -/
theorem telescope (a m : ℕ) :
    a * ∏ i ∈ range m, ((a + 1) ^ 2 ^ i + 1) = (a + 1) ^ 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih]
    obtain ⟨Y, hY⟩ : ∃ Y, (a + 1) ^ 2 ^ m = Y + 1 :=
      ⟨(a + 1) ^ 2 ^ m - 1, by have := Nat.one_le_pow (2 ^ m) (a + 1) (by omega); omega⟩
    have h2 : (a + 1) ^ 2 ^ (m + 1) = ((a + 1) ^ 2 ^ m) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [h2, hY]
    simp only [Nat.add_sub_cancel]
    have h3 : (Y + 1) ^ 2 = Y * Y + 2 * Y + 1 := by ring
    rw [h3]
    ring_nf
    omega

/-- **Nielsen 2015, Lemma 1.3.** `F_s(y) = y^{2^s} - y^{2^{s-1}}` is monotone. -/
theorem Fmono (s y z : ℕ) (hyz : y ≤ z) :
    y ^ 2 ^ (s + 1) - y ^ 2 ^ s ≤ z ^ 2 ^ (s + 1) - z ^ 2 ^ s := by
  have e : ∀ w : ℕ, w ^ 2 ^ (s + 1) - w ^ 2 ^ s = w ^ 2 ^ s * (w ^ 2 ^ s - 1) := by
    intro w
    rw [Nat.mul_sub, mul_one, ← pow_add]
    congr 2
    rw [pow_succ]
    omega
  rw [e, e]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hyz _)
    (by have := Nat.pow_le_pow_left hyz (2 ^ s); omega)

/-- The extremal sequence of Lemma 1.4 has `∏ (1 - 1/n_i) = a/(a+1)`. -/
theorem prodG (q : ℝ) (hq : 1 < q) (m : ℕ) :
    (∏ i ∈ range m, (1 - 1 / (q ^ 2 ^ i + 1))) * (1 - 1 / q ^ 2 ^ m) = (q - 1) / q := by
  have hq0 : q ≠ 0 := by linarith
  induction m with
  | zero => simp; field_simp
  | succ m ih =>
    have hX : 1 < q ^ 2 ^ m := one_lt_pow₀ hq (by positivity)
    have h2 : q ^ 2 ^ (m + 1) = (q ^ 2 ^ m) ^ 2 := by rw [← pow_mul, pow_succ]
    rw [Finset.prod_range_succ, h2, mul_assoc]
    have key : (1 - 1 / (q ^ 2 ^ m + 1)) * (1 - 1 / (q ^ 2 ^ m) ^ 2) = 1 - 1 / q ^ 2 ^ m := by
      set X := q ^ 2 ^ m with hXdef
      have h1 : X + 1 ≠ 0 := by linarith
      have h3 : X ≠ 0 := by linarith
      field_simp
      ring
    rw [key, ih]

private theorem div_helper1 {R Q A B : ℝ} (hR : 0 < R) (hB : 0 < B) (h : R * Q ≤ A / B) :
    Q ≤ A / (B * R) := by
  rw [le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ hB] at h
  nlinarith

private theorem div_helper2 {R Q A B : ℝ} (hR : 0 < R) (hB : 0 < B) (h : A / B < R * Q) :
    A / (B * R) < Q := by
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hB] at h
  nlinarith

/-- **Nielsen 2015, Lemma 1.4** (a strengthening of Lemma 1 of Nielsen 2003). -/
theorem nielsen_lemma14 (r : ℕ) : ∀ (a b : ℕ) (x : ℕ → ℕ), 0 < r → 0 < a → 0 < b →
    (∀ i < r, 1 < x i) → (∀ i, i + 1 < r → x i ≤ x (i + 1)) →
    (∏ i ∈ range r, (1 - 1 / (x i : ℝ)) ≤ (a : ℝ) / b) →
    ((a : ℝ) / b < ∏ i ∈ range (r - 1), (1 - 1 / (x i : ℝ))) →
    a * ∏ i ∈ range r, x i ≤ (a + 1) ^ 2 ^ r - (a + 1) ^ 2 ^ (r - 1) := by
  induction r using Nat.strong_induction_on with
  | _ r IH =>
  intro a b x hr ha hb hx1 hxmono h1 h2
  have hxpos : ∀ i < r, 0 < x i := fun i hi => lt_trans Nat.zero_lt_one (hx1 i hi)
  have hxR : ∀ i < r, (1 : ℝ) < (x i : ℝ) := fun i hi => by exact_mod_cast hx1 i hi
  have hRid : ∀ u ≤ r, ∏ i ∈ range u, (1 - 1 / (x i : ℝ))
      = ((∏ i ∈ range u, (x i - 1) : ℕ) : ℝ) / ((∏ i ∈ range u, x i : ℕ) : ℝ) := by
    intro u hu
    push_cast
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    have hxi : (1 : ℝ) < (x i : ℝ) := hxR i (by omega)
    have hc : ((x i - 1 : ℕ) : ℝ) = (x i : ℝ) - 1 := by
      have h1i : 1 ≤ x i := hx1 i (by omega) |>.le
      push_cast [h1i]
      ring
    rw [hc]
    field_simp
  by_contra hcon
  push_neg at hcon
  -- Step A: lower bounds on all the partial products of `x`.
  have stepA : ∀ u, u ≤ r - 1 → (a + 1) ^ 2 ^ u - 1 ≤ a * ∏ i ∈ range u, x i := by
    intro u hu
    rcases Nat.eq_zero_or_pos u with rfl | hu0
    · simp
    by_contra hlt
    push_neg at hlt
    have hPpos : 0 < ∏ i ∈ range u, x i :=
      Finset.prod_pos fun i hi => hxpos i (by rw [mem_range] at hi; omega)
    have hP'pos : 0 < ∏ i ∈ range u, (x i - 1) := Finset.prod_pos fun i hi => by
      rw [mem_range] at hi; have := hx1 i (by omega); omega
    set P : ℕ := ∏ i ∈ range u, x i with hP
    set P' : ℕ := ∏ i ∈ range u, (x i - 1) with hP'
    set r' : ℕ := r - u with hr'def
    have hr'pos : 0 < r' := by omega
    have hr'lt : r' < r := by omega
    set y : ℕ → ℕ := fun j => x (u + j) with hydef
    have hR : ∏ i ∈ range u, (1 - 1 / (x i : ℝ)) = (P' : ℝ) / (P : ℝ) := hRid u (by omega)
    have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPpos
    have hP'R : (0 : ℝ) < (P' : ℝ) := by exact_mod_cast hP'pos
    have hRpos : (0 : ℝ) < (P' : ℝ) / (P : ℝ) := by positivity
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have habeq : (a : ℝ) / ((b : ℝ) * ((P' : ℝ) / (P : ℝ)))
        = ((a * P : ℕ) : ℝ) / ((b * P' : ℕ) : ℝ) := by
      push_cast
      field_simp
    have h1' : ∏ j ∈ range r', (1 - 1 / (y j : ℝ)) ≤ ((a * P : ℕ) : ℝ) / ((b * P' : ℕ) : ℝ) := by
      rw [← habeq]
      refine div_helper1 hRpos hbR ?_
      rw [← hR, ← Finset.prod_range_add]
      rw [show u + r' = r by omega]
      exact h1
    have h2' : ((a * P : ℕ) : ℝ) / ((b * P' : ℕ) : ℝ)
        < ∏ j ∈ range (r' - 1), (1 - 1 / (y j : ℝ)) := by
      rw [← habeq]
      refine div_helper2 hRpos hbR ?_
      rw [← hR, ← Finset.prod_range_add]
      rw [show u + (r' - 1) = r - 1 by omega]
      exact h2
    have hIH := IH r' hr'lt (a * P) (b * P') y hr'pos (Nat.mul_pos ha hPpos)
      (Nat.mul_pos hb hP'pos) (fun j hj => hx1 (u + j) (by omega))
      (fun j hj => hxmono (u + j) (by omega)) h1' h2'
    -- rewrite the left-hand side
    have hprod : ∏ i ∈ range r, x i = P * ∏ j ∈ range r', y j := by
      rw [hP, hydef, ← Finset.prod_range_add, show u + r' = r by omega]
    have hstep : a * ∏ i ∈ range r, x i = (a * P) * ∏ j ∈ range r', y j := by
      rw [hprod, mul_assoc]
    have hbound : a * P + 1 ≤ (a + 1) ^ 2 ^ u := by omega
    have hFm := Fmono (r' - 1) (a * P + 1) ((a + 1) ^ 2 ^ u) hbound
    rw [show r' - 1 + 1 = r' by omega] at hFm
    have hpow1 : ((a + 1) ^ 2 ^ u) ^ 2 ^ r' = (a + 1) ^ 2 ^ r := by
      rw [← pow_mul, ← pow_add, show u + r' = r by omega]
    have hpow2 : ((a + 1) ^ 2 ^ u) ^ 2 ^ (r' - 1) = (a + 1) ^ 2 ^ (r - 1) := by
      rw [← pow_mul, ← pow_add, show u + (r' - 1) = r - 1 by omega]
    rw [hpow1, hpow2] at hFm
    omega
  -- the extremal sequence
  set nn : ℕ → ℕ := fun i => if i + 1 < r then (a + 1) ^ 2 ^ i + 1 else (a + 1) ^ 2 ^ (r - 1)
    with hnn
  have hq2 : ∀ s : ℕ, 2 ≤ (a + 1) ^ 2 ^ s := by
    intro s
    calc 2 ≤ a + 1 := by omega
      _ = (a + 1) ^ 1 := (pow_one _).symm
      _ ≤ (a + 1) ^ 2 ^ s := Nat.pow_le_pow_right (by omega) (Nat.one_le_two_pow)
  have hnn1 : ∀ i, 1 < nn i := by
    intro i
    rw [hnn]
    dsimp only
    split
    · have := hq2 i; omega
    · exact hq2 (r - 1)
  have hnnpre : ∀ u ≤ r - 1, ∏ i ∈ range u, nn i = ∏ i ∈ range u, ((a + 1) ^ 2 ^ i + 1) := by
    intro u hu
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [hnn]
    dsimp only
    rw [if_pos (by omega)]
  have hnnA : ∀ u ≤ r - 1, a * ∏ i ∈ range u, nn i = (a + 1) ^ 2 ^ u - 1 := by
    intro u hu
    rw [hnnpre u hu, telescope]
  have hnnfull : a * ∏ i ∈ range r, nn i = (a + 1) ^ 2 ^ r - (a + 1) ^ 2 ^ (r - 1) := by
    have hsplit : ∏ i ∈ range r, nn i = (∏ i ∈ range (r - 1), nn i) * nn (r - 1) := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega]
      rw [Finset.prod_range_succ]
    have hlast : nn (r - 1) = (a + 1) ^ 2 ^ (r - 1) := by
      rw [hnn]; dsimp only; rw [if_neg (by omega)]
    rw [hsplit, hlast, ← mul_assoc, hnnA (r - 1) le_rfl]
    have hX : 2 ≤ (a + 1) ^ 2 ^ (r - 1) := hq2 (r - 1)
    have htwo : 2 ^ r = 2 ^ (r - 1) + 2 ^ (r - 1) := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega]
      rw [pow_succ]
      omega
    have hpow : (a + 1) ^ 2 ^ r = (a + 1) ^ 2 ^ (r - 1) * (a + 1) ^ 2 ^ (r - 1) := by
      rw [htwo, pow_add]
    rw [hpow, Nat.sub_mul, one_mul]
  have hnnmono : ∀ i, i + 1 < r → nn i ≤ nn (i + 1) := by
    intro i hi
    rw [hnn]
    dsimp only
    by_cases hc : i + 1 + 1 < r
    · rw [if_pos (by omega), if_pos hc]
      have : (a + 1) ^ 2 ^ i ≤ (a + 1) ^ 2 ^ (i + 1) :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      omega
    · rw [if_pos (by omega), if_neg hc]
      have hir : i + 1 = r - 1 := by omega
      rw [← hir]
      have hX : 2 ≤ (a + 1) ^ 2 ^ i := hq2 i
      have hsq : (a + 1) ^ 2 ^ (i + 1) = (a + 1) ^ 2 ^ i * (a + 1) ^ 2 ^ i := by
        rw [← pow_add]
        congr 1
        rw [pow_succ]
        omega
      nlinarith
  -- partial products comparison
  have hcmp : ∀ u ≤ r, ∏ i ∈ range u, nn i ≤ ∏ i ∈ range u, x i := by
    intro u hu
    rcases Nat.lt_or_ge u r with h | h
    · have hA := stepA u (by omega)
      have hB := hnnA u (by omega)
      have : a * ∏ i ∈ range u, nn i ≤ a * ∏ i ∈ range u, x i := by omega
      exact Nat.le_of_mul_le_mul_left this ha
    · have hueq : u = r := by omega
      subst hueq
      have : a * ∏ i ∈ range u, nn i ≤ a * ∏ i ∈ range u, x i := by omega
      exact Nat.le_of_mul_le_mul_left this ha
  have hcmplt : ∏ i ∈ range r, nn i < ∏ i ∈ range r, x i := by
    have : a * ∏ i ∈ range r, nn i < a * ∏ i ∈ range r, x i := by omega
    exact lt_of_mul_lt_mul_left this (Nat.zero_le a)
  -- apply the majorization lemma
  have hmaj : ∏ i ∈ range r, (1 - 1 / (nn i : ℝ)) < ∏ i ∈ range r, (1 - 1 / (x i : ℝ)) := by
    refine prod_one_sub_inv_lt_of_prod_lt r (fun i => (nn i : ℝ)) (fun i => (x i : ℝ)) hr
      ?_ ?_ ?_ ?_ ?_
    · intro i _
      show (1 : ℝ) < (nn i : ℝ)
      exact_mod_cast hnn1 i
    · intro i hi
      show (1 : ℝ) < (x i : ℝ)
      exact hxR i hi
    · intro i hi
      show ((x i : ℝ)) ≤ ((x (i + 1) : ℝ))
      exact_mod_cast hxmono i hi
    · intro m hm
      show ∏ i ∈ range m, ((nn i : ℝ)) ≤ ∏ i ∈ range m, ((x i : ℝ))
      exact_mod_cast hcmp m hm
    · show ∏ i ∈ range r, ((nn i : ℝ)) < ∏ i ∈ range r, ((x i : ℝ))
      exact_mod_cast hcmplt
  -- compute the extremal product
  have hextr : ∏ i ∈ range r, (1 - 1 / (nn i : ℝ)) = (a : ℝ) / (a + 1) := by
    have hsplit : ∏ i ∈ range r, (1 - 1 / (nn i : ℝ))
        = (∏ i ∈ range (r - 1), (1 - 1 / (nn i : ℝ))) * (1 - 1 / (nn (r - 1) : ℝ)) := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega]
      rw [Finset.prod_range_succ]
    have hlast : nn (r - 1) = (a + 1) ^ 2 ^ (r - 1) := by
      rw [hnn]; dsimp only; rw [if_neg (by omega)]
    have hpre : ∀ i < r - 1, ((nn i : ℝ)) = ((a : ℝ) + 1) ^ 2 ^ i + 1 := by
      intro i hi
      rw [hnn]; dsimp only; rw [if_pos (by omega)]
      push_cast
      ring
    rw [hsplit, hlast]
    have h1eq : ∏ i ∈ range (r - 1), (1 - 1 / (nn i : ℝ))
        = ∏ i ∈ range (r - 1), (1 - 1 / (((a : ℝ) + 1) ^ 2 ^ i + 1)) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [mem_range] at hi
      rw [hpre i hi]
    rw [h1eq]
    have hcast : (((a + 1) ^ 2 ^ (r - 1) : ℕ) : ℝ) = ((a : ℝ) + 1) ^ 2 ^ (r - 1) := by push_cast; ring
    rw [hcast]
    have := prodG ((a : ℝ) + 1) (by
      have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      linarith) (r - 1)
    rw [this]
    ring
  rw [hextr] at hmaj
  have hfinal : (a : ℝ) / ((a : ℝ) + 1) < (a : ℝ) / (b : ℝ) := lt_of_lt_of_le hmaj h1
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hba : (b : ℝ) < (a : ℝ) + 1 := by
    by_contra hle
    push_neg at hle
    have : (a : ℝ) / (b : ℝ) ≤ (a : ℝ) / ((a : ℝ) + 1) :=
      div_le_div_of_nonneg_left haR.le (by linarith) hle
    linarith
  have hbn : b ≤ a := by
    have : (b : ℝ) < (a : ℝ) + 1 := hba
    have : b < a + 1 := by exact_mod_cast this
    omega
  -- but h2 forces a < b
  have hle1 : ∏ i ∈ range (r - 1), (1 - 1 / (x i : ℝ)) ≤ 1 := by
    refine Finset.prod_le_one (fun i hi => ?_) (fun i hi => ?_)
    · rw [mem_range] at hi
      have := hxR i (by omega)
      have h0 : (0:ℝ) < (x i : ℝ) := by linarith
      have : 1 / (x i : ℝ) ≤ 1 := by
        rw [div_le_one h0]; linarith
      linarith
    · have h0 : (0:ℝ) < (x i : ℝ) := by
        rw [mem_range] at hi; linarith [hxR i (show i < r by omega)]
      have : 0 < 1 / (x i : ℝ) := by positivity
      linarith
  have : (a : ℝ) / (b : ℝ) < 1 := lt_of_lt_of_le h2 hle1
  rw [div_lt_one hbR] at this
  have : a < b := by exact_mod_cast this
  omega


theorem solution (r a b : ℕ) (x : ℕ → ℕ) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hx1 : ∀ i < r, 1 < x i) (hxmono : ∀ i, i + 1 < r → x i ≤ x (i + 1))
    (h1 : ∏ i ∈ Finset.range r, (1 - 1 / (x i : ℝ)) ≤ (a : ℝ) / b)
    (h2 : (a : ℝ) / b < ∏ i ∈ Finset.range (r - 1), (1 - 1 / (x i : ℝ))) :
    a * ∏ i ∈ Finset.range r, x i ≤ (a + 1) ^ 2 ^ r - (a + 1) ^ 2 ^ (r - 1) :=
  nielsen_lemma14 r a b x hr ha hb hx1 hxmono h1 h2
