-- Prove2me | solution 1 for TokenFinance.MoralHazard.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T13:49:03.791528+00:00
-- url     : https://prove2.me/submissions/c6b82ee2-9bdf-49e6-b46a-cd47ec84add9

/-
DS19M proof of the MoralHazard milestone `TokenFinance.MoralHazard.corollary_2`
(theorem_id f33a5a3c-c3cd-4ac2-a1b1-534aad6aa580): Corollary 2, p. 30 — every project
financeable by equity under moral hazard is financeable by debt, and the converse fails.

Mathematics.  Let `λ = (θl−c)/(θh−c) ∈ (0,1)`.

* Inclusion.  Proposition 5 (Proved) turns `EquityFinanceable` into
  `NPV_h − C_e ≥ λ³(θh/θl)NPV_h`.  Let `D` be the break-even repayment of (21), which exists
  by contract_terms_exist (Proved), and put `δ = 2√D/(θh−c)`.  If `λ ≤ δ`, Proposition 6
  (Proved) gives debt financeability directly.  If `δ < λ`, Lemma 4 (Proved) gives
  `λ³ > (λ−δ)²(λ+2δ)/((1−δ)²(1+2δ))`; multiplying by `(θh/θl)NPV_h > 0` and combining with
  the equity inequality yields the debt incentive constraint (24), and Proposition 6 then
  produces the witnessing repayment `D`.

* Strictness.  For `C₀ = 110`, `c = 10`, `θl = 50`, `θh = 60`, `C_e = 25` the debt contract
  is financeable while equity is not.  The standing assumptions hold
  (`NPV_h = 1145/18 > 25`, `NPV_l = −10/3 ≤ 0`).  Equity fails because
  `NPV_h − C_e = 695/18 < (4/5)³(6/5)(1145/18) = 439680/11250` (Proposition 5).  Debt succeeds
  because the cubic relation (48) forces `29/50 < δ < 3/5` for the break-even `δ`, which makes
  the factor in (24) smaller than `(110/441)(6/5)(1145/18) < 695/18`; Proposition 6 then gives
  `DebtFinanceable`.

No rounded numerical root is used: every bound is an exact rational inequality in Lean.
-/
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable
import Theorems.Thm_TokenFinance_Debt_eq_3
import Theorems.Thm_TokenFinance_Debt_proposition_2
import Theorems.Thm_TokenFinance_MoralHazard_eq_48
import Theorems.Thm_TokenFinance_MoralHazard_contract_terms_exist
import Theorems.Thm_TokenFinance_MoralHazard_proposition_5
import Theorems.Thm_TokenFinance_MoralHazard_proposition_6
import Theorems.Thm_TokenFinance_MoralHazard_lemma_4

open TokenFinance.MoralHazard

/-- The cubic `1250δ³ − 1875δ² + 396` satisfied by the break-even `δ` when `θh = 60`,
`c = 10`, `C₀ = 110`. -/
private def debtPoly (x : ℝ) : ℝ := 1250 * x ^ 3 - 1875 * x ^ 2 + 396

private lemma debtPoly_strictAnti : ∀ x y : ℝ, 0 < x → x < y → y < 1 → debtPoly y < debtPoly x := by
  intro x y hx hxy hy
  unfold debtPoly
  have hx1 : x < 1 := lt_trans hxy hy
  have h1 : x ^ 2 < x := by nlinarith
  have h2 : y ^ 2 < y := by nlinarith
  have h3 : x * y < x := by nlinarith
  have h4 : x * y < y := by nlinarith
  have hkey : 1250 * (x ^ 2 + x * y + y ^ 2) < 1875 * (x + y) := by nlinarith
  nlinarith [hkey, hxy]

theorem solution :
    (∀ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh →
      EquityFinanceable c C0 Ce θl θh → DebtFinanceable c C0 Ce θl θh) ∧
    (∃ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh ∧
      DebtFinanceable c C0 Ce θl θh ∧ ¬ EquityFinanceable c C0 Ce θl θh) := by
  constructor
  · intro c C0 Ce θl θh hA hEq
    have hAkeep : MHAssumptions c C0 Ce θl θh := hA
    obtain ⟨hc, hcl, hlh, hC0, hnpvl, hnpvh, hCe⟩ := hA
    have hcθh : c < θh := lt_trans hcl hlh
    have hθh : 0 < θh := lt_trans hc hcθh
    have hθl : 0 < θl := lt_trans hc hcl
    have hL : 0 < θh - c := by linarith
    set lam : ℝ := (θl - c) / (θh - c) with hlamdef
    have hlam1 : lam < 1 := by
      rw [hlamdef, div_lt_one hL]
      linarith
    have h5 := (TokenFinance.MoralHazard.proposition_5 c C0 Ce θl θh lam hc hcl hlh hC0
      hnpvh hlamdef).mp hEq
    obtain ⟨D, ⟨hD0, hDBE⟩, -⟩ :=
      (TokenFinance.MoralHazard.contract_terms_exist c C0 θh hc hcθh hC0 hnpvh).1
    obtain ⟨hDC0, hD625, -⟩ :=
      (TokenFinance.Debt.proposition_2 c C0 θh hc hcθh hC0 hnpvh).2 D hD0 hDBE
    have hDpos : 0 < D := lt_trans hC0 hDC0
    set δ : ℝ := 2 * Real.sqrt D / (θh - c) with hδdef
    have hδpos : 0 < δ := by
      have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
      rw [hδdef]
      exact div_pos (by linarith) hL
    have h6 := TokenFinance.MoralHazard.proposition_6 c C0 Ce θl θh D δ lam hAkeep hD0 hDBE
      hδdef hlamdef
    by_cases hcase : lam ≤ δ
    · exact (h6.1 hcase).2
    · push_neg at hcase
      refine ⟨D, hD0, hDBE, ?_⟩
      refine (h6.2 hcase).mpr ?_
      have h4 := TokenFinance.MoralHazard.lemma_4 δ lam hδpos hcase hlam1
      have hK : 0 < (θh / θl) * TokenFinance.Debt.npv c C0 θh :=
        mul_pos (div_pos hθh hθl) hnpvh
      have hmul := mul_lt_mul_of_pos_right h4 hK
      nlinarith [hmul, h5]
  · -- the θh = 60, θl = 50, C₀ = 110, c = 10, C_e = 25 instance
    have hnpv60 : TokenFinance.Debt.npv 10 110 60 = 1145 / 18 := by
      rw [TokenFinance.Debt.eq_3 10 110 60 (by norm_num) (by norm_num)]
      norm_num
    have hnpv50 : TokenFinance.Debt.npv 10 110 50 = -10 / 3 := by
      rw [TokenFinance.Debt.eq_3 10 110 50 (by norm_num) (by norm_num)]
      norm_num
    have hnpvpos : 0 < TokenFinance.Debt.npv 10 110 60 := by
      rw [hnpv60]
      norm_num
    have hMH : MHAssumptions 10 110 25 50 60 := by
      refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
      · rw [hnpv50]; norm_num
      · rw [hnpv60]; norm_num
      · rw [hnpv60]; norm_num
    refine ⟨10, 110, 25, 50, 60, hMH, ?_, ?_⟩
    · obtain ⟨D, ⟨hD0, hDBE⟩, -⟩ :=
        (TokenFinance.MoralHazard.contract_terms_exist 10 110 60 (by norm_num) (by norm_num)
          (by norm_num) hnpvpos).1
      obtain ⟨hD110, hD625, -⟩ :=
        (TokenFinance.Debt.proposition_2 10 110 60 (by norm_num) (by norm_num) (by norm_num)
          hnpvpos).2 D hD0 hDBE
      have hD625' : D < 625 := by
        have := hD625
        norm_num at this
        linarith
      set δ : ℝ := 2 * Real.sqrt D / (60 - 10) with hδdef
      have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
      have hδ1 : δ < 1 := by
        rw [hδdef]
        have hsqrt : Real.sqrt D < 25 := by
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 25)]
          linarith
        rw [div_lt_one (by norm_num : (0 : ℝ) < 60 - 10)]
        linarith
      have h48 := TokenFinance.MoralHazard.eq_48 10 110 60 D δ (by norm_num) (by norm_num)
        (by norm_num) hnpvpos hD0 hDBE hδdef
      have hcub : 1 - 3 * δ ^ 2 + 2 * δ ^ 3 = 229 / 625 := by
        have h := h48.2
        rw [hnpv60] at h
        have hcoef : (60 - 10 : ℝ) ^ 3 / (12 * 60) = 3125 / 18 := by norm_num
        rw [hcoef] at h
        field_simp at h
        linarith
      have hpoly : debtPoly δ = 0 := by
        unfold debtPoly
        nlinarith [hcub]
      have hδpos : 0 < δ := by
        rcases eq_or_lt_of_le hδ0 with h | h
        · rw [← h] at hpoly
          norm_num [debtPoly] at hpoly
        · exact h
      have hf29 : 0 < debtPoly (29 / 50) := by norm_num [debtPoly]
      have hf35 : debtPoly (3 / 5) < 0 := by norm_num [debtPoly]
      have hδlt : δ < 3 / 5 := by
        by_contra hcon
        push_neg at hcon
        rcases lt_or_eq_of_le hcon with h | h
        · have hdec := debtPoly_strictAnti (3 / 5) δ (by norm_num) h hδ1
          rw [hpoly] at hdec
          linarith
        · rw [← h] at hpoly
          linarith
      have hδgt : 29 / 50 < δ := by
        by_contra hcon
        push_neg at hcon
        rcases lt_or_eq_of_le hcon with h | h
        · have hdec := debtPoly_strictAnti δ (29 / 50) hδpos h (by norm_num)
          rw [hpoly] at hdec
          linarith
        · rw [h] at hpoly
          linarith
      have h6 := TokenFinance.MoralHazard.proposition_6 10 110 25 50 60 D δ (4 / 5) hMH
        hD0 hDBE hδdef (by norm_num)
      by_cases hcase : (4 / 5 : ℝ) ≤ δ
      · exact (h6.1 hcase).2
      · push_neg at hcase
        refine ⟨D, hD0, hDBE, ?_⟩
        refine (h6.2 hcase).mpr ?_
        rw [hnpv60]
        have hden : 0 < 1 - δ := by linarith
        have hnum : 0 < 4 / 5 - δ := by linarith
        have hA : (4 / 5 - δ) ^ 2 / (1 - δ) ^ 2 < 121 / 441 := by
          have hratio : (4 / 5 - δ) / (1 - δ) < 11 / 21 := by
            rw [div_lt_iff₀ hden]
            nlinarith [hδgt]
          have hsq : ((4 / 5 - δ) / (1 - δ)) ^ 2 < (11 / 21) ^ 2 :=
            pow_lt_pow_left₀ hratio (le_of_lt (div_pos hnum hden)) (by norm_num)
          have hsq' : ((4 / 5 - δ) / (1 - δ)) ^ 2 < 121 / 441 := by
            have hval : (11 / 21 : ℝ) ^ 2 = 121 / 441 := by norm_num
            linarith
          have hEq : (4 / 5 - δ) ^ 2 / (1 - δ) ^ 2 = ((4 / 5 - δ) / (1 - δ)) ^ 2 := by
            rw [div_pow]
          rw [hEq]
          exact hsq'
        have hB : (4 / 5 + 2 * δ) / (1 + 2 * δ) < 10 / 11 := by
          have hd : 0 < 1 + 2 * δ := by linarith
          rw [div_lt_iff₀ hd]
          nlinarith [hδlt]
        have hBpos : 0 < (4 / 5 + 2 * δ) / (1 + 2 * δ) := by
          apply div_pos <;> linarith
        have hAB : (4 / 5 - δ) ^ 2 / (1 - δ) ^ 2 * ((4 / 5 + 2 * δ) / (1 + 2 * δ)) <
            121 / 441 * (10 / 11) := by
          have h1 := mul_lt_mul_of_pos_right hA hBpos
          have h2 := mul_lt_mul_of_pos_left hB (by norm_num : (0 : ℝ) < 121 / 441)
          linarith
        have hstep : (4 / 5 - δ) ^ 2 / (1 - δ) ^ 2 * ((4 / 5 + 2 * δ) / (1 + 2 * δ)) *
              ((60 : ℝ) / 50) * (1145 / 18) < (110 / 441) * ((60 : ℝ) / 50) * (1145 / 18) := by
          have hk : 0 < ((60 : ℝ) / 50) * (1145 / 18) := by norm_num
          have h := mul_lt_mul_of_pos_right hAB hk
          have hval : 121 / 441 * (10 / 11) = 110 / 441 := by norm_num
          nlinarith [h, hval]
        have hnum2 : (110 / 441) * ((60 : ℝ) / 50) * (1145 / 18) < (1145 / 18) - 25 := by
          norm_num
        linarith
    · intro hEq
      have h5 := (TokenFinance.MoralHazard.proposition_5 10 110 25 50 60 (4 / 5) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) hnpvpos (by norm_num)).mp hEq
      rw [hnpv60] at h5
      norm_num at h5
