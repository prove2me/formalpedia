-- Prove2me | solution 1 for ProductSupport.PBCFirstBest.proposition_5_i
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T09:08:23.243118+00:00
-- url     : https://prove2.me/submissions/392c4ffd-1920-4038-b463-e3938a2ae6ba

import Mathlib
import Definitions.Def_ProductSupport_PBCFirstBest_Model

open ProductSupport.PBCFirstBest in
lemma pbc_mu0_pos (P : Params) (hS : P.Standing) {lam : ℝ} (hl : 0 < lam) :
    0 < mu0 P lam := by
  obtain ⟨hr, hc, -, -, -, -, -, -, -⟩ := hS
  unfold mu0
  exact Real.sqrt_pos.mpr (div_pos (mul_pos hr hl) hc)

open ProductSupport.PBCFirstBest in
lemma pbc_mu0_sq (P : Params) (hS : P.Standing) {lam : ℝ} (hl : 0 < lam) :
    mu0 P lam ^ 2 = P.r * lam / P.c := by
  obtain ⟨hr, hc, -, -, -, -, -, -, -⟩ := hS
  unfold mu0
  exact Real.sq_sqrt (le_of_lt (div_pos (mul_pos hr hl) hc))

open ProductSupport.PBCFirstBest in
lemma pbc_cust_v0 (P : Params) (lam lam' M : ℝ) (hm : mu0 P lam ≠ 0)
    (hml : mu0 P lam - lam ≠ 0) :
    custPayoff P lam' ⟨v0 P lam M, mu0 P lam⟩ =
      M * (mu0 P lam - lam') / (mu0 P lam - lam) := by
  unfold custPayoff uptime v0
  simp only
  field_simp
  ring

open ProductSupport.PBCFirstBest in
lemma pbc_supp_eq (P : Params) (lam : ℝ) (k : Contract) :
    suppPayoff P lam k = scProfit P lam k.mu - custPayoff P lam k := by
  unfold suppPayoff scProfit custPayoff
  ring

open ProductSupport.PBCFirstBest in
lemma pbc_sc_le (P : Params) (hS : P.Standing) {lam mu : ℝ} (hl : 0 < lam) (hmu : 0 < mu) :
    scProfit P lam mu ≤ scProfit P lam (mu0 P lam) := by
  have hc : 0 < P.c := hS.2.1
  have h0 := pbc_mu0_pos P hS hl
  have hsq := pbc_mu0_sq P hS hl
  have hrl : P.r * lam = P.c * mu0 P lam ^ 2 := by
    rw [hsq]; field_simp
  unfold scProfit uptime
  have key : P.r * lam / mu + P.c * mu ≥ P.r * lam / mu0 P lam + P.c * mu0 P lam := by
    rw [hrl]
    have e1 : P.c * mu0 P lam ^ 2 / mu0 P lam + P.c * mu0 P lam = 2 * P.c * mu0 P lam := by
      field_simp; ring
    have e2 : P.c * mu0 P lam ^ 2 / mu + P.c * mu - 2 * P.c * mu0 P lam
        = P.c * (mu - mu0 P lam) ^ 2 / mu := by
      field_simp; ring
    have : 0 ≤ P.c * (mu - mu0 P lam) ^ 2 / mu := by positivity
    linarith
  have a1 : P.r * (1 - lam / mu) = P.r - P.r * lam / mu := by ring
  have a2 : P.r * (1 - lam / mu0 P lam) = P.r - P.r * lam / mu0 P lam := by ring
  rw [a1, a2]
  linarith

open ProductSupport.PBCFirstBest in
theorem solution (P : Params) (hS : P.Standing) (h10 : Cond10 P)
    (hvL : 0 < v0 P P.lamL P.ML) (hvH : 0 < v0 P P.lamH P.MH) :
    (fbMenu P).Feasible P ∧
    (∀ m : Menu, m.Feasible P →
      objective P m ≤ objective P (fbMenu P)) ∧
    custPayoff P P.lamL (fbMenu P).L = P.ML ∧
    custPayoff P P.lamH (fbMenu P).H = P.MH ∧
    (fbMenu P).L.mu < (fbMenu P).H.mu := by
  obtain ⟨hr, hc, hcr, hlL, hLH, hb0, hb1, hMH, hMLH⟩ := hS
  have hS : P.Standing := ⟨hr, hc, hcr, hlL, hLH, hb0, hb1, hMH, hMLH⟩
  have hlH : 0 < P.lamH := lt_trans hlL hLH
  have hmL := pbc_mu0_pos P hS hlL
  have hmH := pbc_mu0_pos P hS hlH
  have sqL := pbc_mu0_sq P hS hlL
  have sqH := pbc_mu0_sq P hS hlH
  obtain ⟨c1, c2⟩ := h10
  have hratio : 1 < P.ML / P.MH := by
    rw [lt_div_iff₀ hMH]; linarith
  -- mu0 L > lamH
  have hbL : P.lamH < mu0 P P.lamL := by
    by_contra hcon0
    have hcon := not_lt.mp hcon0
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have hb : mu0 P P.lamL - P.lamH < 0 := by linarith
      have : (mu0 P P.lamL - P.lamL) / (mu0 P P.lamL - P.lamH) ≤ 1 := by
        rw [div_le_one_of_neg hb]; linarith
      linarith
    · have : mu0 P P.lamL - P.lamH = 0 := by linarith
      rw [this, div_zero] at c2
      linarith
  have hsqlt : mu0 P P.lamL ^ 2 < mu0 P P.lamH ^ 2 := by
    rw [sqL, sqH]
    apply div_lt_div_of_pos_right _ hc
    exact mul_lt_mul_of_pos_left hLH hr
  have hmLH : mu0 P P.lamL < mu0 P P.lamH := by
    nlinarith
  have haH : P.lamH < mu0 P P.lamH := lt_trans hbL hmLH
  have hdL : mu0 P P.lamL - P.lamL ≠ 0 := by linarith
  have hdH : mu0 P P.lamH - P.lamH ≠ 0 := by linarith
  have IRL : custPayoff P P.lamL (fbMenu P).L = P.ML := by
    show custPayoff P P.lamL ⟨v0 P P.lamL P.ML, mu0 P P.lamL⟩ = P.ML
    rw [pbc_cust_v0 P _ _ _ hmL.ne' hdL]
    field_simp
  have IRH : custPayoff P P.lamH (fbMenu P).H = P.MH := by
    show custPayoff P P.lamH ⟨v0 P P.lamH P.MH, mu0 P P.lamH⟩ = P.MH
    rw [pbc_cust_v0 P _ _ _ hmH.ne' hdH]
    field_simp
  have ICL : custPayoff P P.lamL (fbMenu P).H ≤ custPayoff P P.lamL (fbMenu P).L := by
    rw [IRL]
    show custPayoff P P.lamL ⟨v0 P P.lamH P.MH, mu0 P P.lamH⟩ ≤ P.ML
    rw [pbc_cust_v0 P _ _ _ hmH.ne' hdH]
    have hpos : 0 < mu0 P P.lamH - P.lamH := by linarith
    rw [div_le_div_iff₀ hpos hMH] at c1
    rw [div_le_iff₀ hpos]
    linarith
  have ICH : custPayoff P P.lamH (fbMenu P).L ≤ custPayoff P P.lamH (fbMenu P).H := by
    rw [IRH]
    show custPayoff P P.lamH ⟨v0 P P.lamL P.ML, mu0 P P.lamL⟩ ≤ P.MH
    rw [pbc_cust_v0 P _ _ _ hmL.ne' hdL]
    have hpos : 0 < mu0 P P.lamL - P.lamL := by linarith
    have hpos2 : 0 < mu0 P P.lamL - P.lamH := by linarith
    rw [div_le_div_iff₀ hMH hpos2] at c2
    rw [div_le_iff₀ hpos]
    linarith
  have feas : (fbMenu P).Feasible P :=
    ⟨hvL, hmL, hvH, hmH, IRL.ge, IRH.ge, ICL, ICH⟩
  refine ⟨feas, ?_, IRL, IRH, hmLH⟩
  intro m hm
  obtain ⟨-, hmuL, -, hmuH, irL, irH, -, -⟩ := hm
  unfold objective
  rw [pbc_supp_eq, pbc_supp_eq, pbc_supp_eq P P.lamL (fbMenu P).L,
    pbc_supp_eq P P.lamH (fbMenu P).H, IRL, IRH]
  have s1 := pbc_sc_le P hS hlL hmuL
  have s2 := pbc_sc_le P hS hlH hmuH
  have e1 : (fbMenu P).L.mu = mu0 P P.lamL := rfl
  have e2 : (fbMenu P).H.mu = mu0 P P.lamH := rfl
  rw [e1, e2]
  have hb1' : 0 < 1 - P.β := by linarith
  nlinarith [mul_le_mul_of_nonneg_left s1 hb0.le, mul_le_mul_of_nonneg_left s2 hb1'.le,
    mul_le_mul_of_nonneg_left irL hb0.le, mul_le_mul_of_nonneg_left irH hb1'.le]
