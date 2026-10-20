-- Prove2me | solution 1 for TokenFinance.MoralHazard.appendixB_theta57
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T13:49:34.460286+00:00
-- url     : https://prove2.me/submissions/b34733d5-bd62-4e09-8fb3-c58c1ea03909

/-
DS19M proof of the MoralHazard milestone `TokenFinance.MoralHazard.appendixB_theta57`
(theorem_id d16ac8ee-fc93-4848-a964-5152b734ca4f): Appendix B, pp. 45-47, the instance
`C₀ = 110`, `c = 10`, `θl = 50`, `θh = 57`, `C_e = 25`: the project is financeable by debt
only — not by tokens and not by equity.

Mathematics.  `NPV_h = (57−10)³/(12·57) − 110 = 28583/684 ≈ 41.79` and
`NPV_l = −10/3 ≤ 0`, so the standing assumptions hold (`25 = 17100/684 < 28583/684`).

* Equity fails.  `λ = 40/47`; Proposition 5 makes equity financing equivalent to
  `NPV_h − C_e ≥ λ³(θh/θl)NPV_h`, i.e. `16.79 ≥ 29.37`, which is false.

* Debt succeeds.  The break-even `D` exists and `D < (θh−c)²/4`, so for `a = 2√D` and
  `δ = a/47 = 2√D/(θh−c) ∈ (0,1)` equation (48) gives the exact cubic
  `2a³ − 141a² + 75240 = 0`.  That cubic is strictly decreasing on `(0,47)` with values
  `2340 > 0` at `30` and `−679 < 0` at `31`, so `30 < a < 31`, i.e.
  `30/47 < δ < 31/47`.  Then `((λ−δ)/(1−δ))² < (10/17)²` and
  `(λ+2δ)/(1+2δ) < 102/109`, so the factor of (24) is below
  `(100/289)(102/109)`, and `(100/289)(102/109)(57/50)NPV_h < NPV_h − C_e`; Proposition 6
  then supplies the debt contract.

* Tokens fail.  The unique break-even pre-sale `t` of (16) satisfies
  `G(5) = 50653/1026 > NPV_h > 214375/5472 = G(6)`, so by continuity and uniqueness
  `5 < t < 6`, and `τ = 2t/47 ∈ (10/47, 12/47)`.  Since `τ < 12/47 < λ = 40/47`, the ratio
  `(λ−τ)/(1−τ)` exceeds `(40−12)/(47−12) = 4/5`, so the factor of (29) is above
  `(4/5)³ = 64/125` and its right side exceeds `(64/125)(57/50)NPV_h > NPV_h − C_e`.
  Hence (29) fails at the only possible break-even pre-sale, so no `t` witnesses
  `TokenFinanceable`.
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
import Theorems.Thm_TokenFinance_MoralHazard_proposition_7

open TokenFinance.MoralHazard

/-- The cubic `2a³ − 141a² + 75240` satisfied by `a = 2√D` for the break-even debt contract
when `θh = 57`, `c = 10`, `C₀ = 110`. -/
private def debtPoly57 (x : ℝ) : ℝ := 2 * x ^ 3 - 141 * x ^ 2 + 75240

private lemma debtPoly57_strictAnti :
    ∀ x y : ℝ, 0 < x → x < y → y < 47 → debtPoly57 y < debtPoly57 x := by
  intro x y hx hxy hy
  unfold debtPoly57
  have h1 : x ^ 2 < 47 * x := by nlinarith
  have h2 : x * y < 47 * x := by nlinarith
  have h3 : y ^ 2 < 47 * y := by nlinarith
  have hkey : 2 * (x ^ 2 + x * y + y ^ 2) < 141 * (x + y) := by nlinarith
  nlinarith [hkey, hxy]

/-- The factor of (29) at `θh = 57`, `c = 10`, `C₀ = 110` exceeds `64/125` as soon as
`τ < 12/47`, and then the right-hand side of (29) exceeds `NPV_h − C_e`. -/
private lemma big_factor (τ : ℝ) (hτ12 : τ < 12 / 47) :
    (28583 / 684 : ℝ) - 25 <
      (40 / 47 - τ) ^ 3 / (1 - τ) ^ 3 * ((57 : ℝ) / 50) * (28583 / 684) := by
  have hden : 0 < 1 - τ := by linarith only [hτ12]
  have hratio : (4 / 5 : ℝ) < (40 / 47 - τ) / (1 - τ) := by
    rw [lt_div_iff₀ hden]
    nlinarith only [hτ12]
  have hcube : (4 / 5 : ℝ) ^ 3 < ((40 / 47 - τ) / (1 - τ)) ^ 3 :=
    pow_lt_pow_left₀ hratio (by norm_num) (by norm_num)
  have hEq : (40 / 47 - τ) ^ 3 / (1 - τ) ^ 3 = ((40 / 47 - τ) / (1 - τ)) ^ 3 := by
    rw [div_pow]
  rw [hEq]
  have hk : 0 < ((57 : ℝ) / 50) * (28583 / 684) := by norm_num
  have hmul := mul_lt_mul_of_pos_right hcube hk
  have hbase : (28583 / 684) - 25 <
      (4 / 5 : ℝ) ^ 3 * ((57 : ℝ) / 50) * (28583 / 684) := by norm_num
  linarith only [hbase, hmul]

theorem solution :
    MHAssumptions 10 110 25 50 57 ∧ DebtFinanceable 10 110 25 50 57 ∧
      ¬ TokenFinanceable 10 110 25 50 57 ∧ ¬ EquityFinanceable 10 110 25 50 57 := by
  have hnpv57 : TokenFinance.Debt.npv 10 110 57 = 28583 / 684 := by
    rw [TokenFinance.Debt.eq_3 10 110 57 (by norm_num) (by norm_num)]
    norm_num
  have hnpv50 : TokenFinance.Debt.npv 10 110 50 = -10 / 3 := by
    rw [TokenFinance.Debt.eq_3 10 110 50 (by norm_num) (by norm_num)]
    norm_num
  have hnpvpos : 0 < TokenFinance.Debt.npv 10 110 57 := by
    rw [hnpv57]
    norm_num
  have hMH : MHAssumptions 10 110 25 50 57 := by
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · rw [hnpv50]; norm_num
    · rw [hnpv57]; norm_num
    · rw [hnpv57]; norm_num
  have htV : (57 - 10 : ℝ) ^ 3 / (12 * 57) - 110 = 28583 / 684 := by norm_num
  refine ⟨hMH, ?_, ?_, ?_⟩
  · -- debt financeability via the break-even repayment and Proposition 6
    obtain ⟨D, ⟨hD0, hDBE⟩, -⟩ :=
      (TokenFinance.MoralHazard.contract_terms_exist 10 110 57 (by norm_num) (by norm_num)
        (by norm_num) hnpvpos).1
    obtain ⟨hDC0, hD625, -⟩ :=
      (TokenFinance.Debt.proposition_2 10 110 57 (by norm_num) (by norm_num) (by norm_num)
        hnpvpos).2 D hD0 hDBE
    have hDpos : 0 < D := lt_trans (by norm_num : (0 : ℝ) < 110) hDC0
    have hD552 : D < 552.25 := by
      have h := hD625
      norm_num at h
      linarith
    set a : ℝ := 2 * Real.sqrt D with hadef
    have ha0 : 0 ≤ a := by rw [hadef]; positivity
    have ha47 : a < 47 := by
      rw [hadef]
      have hsqrt : Real.sqrt D < 23.5 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 23.5)]
        nlinarith
      linarith
    set δ : ℝ := 2 * Real.sqrt D / (57 - 10) with hδdef
    have hδdef' : δ = 2 * Real.sqrt D / (57 - 10) := hδdef
    have hδa : δ = a / 47 := by
      rw [hδdef, hadef]
      norm_num
    have hδ0 : 0 ≤ δ := by
      rw [hδa]
      exact div_nonneg ha0 (by norm_num)
    have hδ1 : δ < 1 := by
      rw [hδa, div_lt_one (by norm_num : (0 : ℝ) < 47)]
      linarith
    have h48 := TokenFinance.MoralHazard.eq_48 10 110 57 D δ (by norm_num) (by norm_num)
      (by norm_num) hnpvpos hD0 hDBE hδdef'
    have hcub : 1 - 3 * δ ^ 2 + 2 * δ ^ 3 = 28583 / 103823 := by
      have h := h48.2
      rw [hnpv57] at h
      have hcoef : (57 - 10 : ℝ) ^ 3 / (12 * 57) = 103823 / 684 := by norm_num
      rw [hcoef] at h
      field_simp at h
      linarith
    have hpolyδ : 207646 * δ ^ 3 - 311469 * δ ^ 2 + 75240 = 0 := by
      nlinarith [hcub]
    have hpoly : debtPoly57 a = 0 := by
      unfold debtPoly57
      have hsub : a = δ * 47 := by rw [hδa]; field_simp
      rw [hsub]
      nlinarith [hpolyδ]
    have hapos : 0 < a := by
      rcases eq_or_lt_of_le ha0 with h | h
      · rw [← h] at hpoly
        norm_num [debtPoly57] at hpoly
      · exact h
    have hf30 : 0 < debtPoly57 30 := by norm_num [debtPoly57]
    have hf31 : debtPoly57 31 < 0 := by norm_num [debtPoly57]
    have ha31 : a < 31 := by
      by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with h | h
      · have hdec := debtPoly57_strictAnti 31 a (by norm_num) h ha47
        rw [hpoly] at hdec
        linarith
      · rw [← h] at hpoly
        linarith
    have ha30 : 30 < a := by
      by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with h | h
      · have hdec := debtPoly57_strictAnti a 30 hapos h (by norm_num)
        rw [hpoly] at hdec
        linarith
      · rw [h] at hpoly
        linarith
    have hδgt : 30 / 47 < δ := by
      rw [hδa, lt_div_iff₀ (by norm_num : (0 : ℝ) < 47)]
      linarith
    have hδlt : δ < 31 / 47 := by
      rw [hδa, div_lt_iff₀ (by norm_num : (0 : ℝ) < 47)]
      linarith
    have h6 := TokenFinance.MoralHazard.proposition_6 10 110 25 50 57 D δ (40 / 47) hMH
      hD0 hDBE hδdef' (by norm_num)
    by_cases hcase : (40 / 47 : ℝ) ≤ δ
    · exact (h6.1 hcase).2
    · push_neg at hcase
      refine ⟨D, hD0, hDBE, ?_⟩
      refine (h6.2 hcase).mpr ?_
      rw [hnpv57]
      have hden : 0 < 1 - δ := by linarith
      have hnum : 0 < 40 / 47 - δ := by linarith
      have hA : (40 / 47 - δ) ^ 2 / (1 - δ) ^ 2 < 100 / 289 := by
        have hratio : (40 / 47 - δ) / (1 - δ) < 10 / 17 := by
          rw [div_lt_iff₀ hden]
          nlinarith [hδgt]
        have hsq : ((40 / 47 - δ) / (1 - δ)) ^ 2 < (10 / 17) ^ 2 :=
          pow_lt_pow_left₀ hratio (le_of_lt (div_pos hnum hden)) (by norm_num)
        have hsq' : ((40 / 47 - δ) / (1 - δ)) ^ 2 < 100 / 289 := by
          have hval : (10 / 17 : ℝ) ^ 2 = 100 / 289 := by norm_num
          linarith
        have hEq : (40 / 47 - δ) ^ 2 / (1 - δ) ^ 2 = ((40 / 47 - δ) / (1 - δ)) ^ 2 := by
          rw [div_pow]
        rw [hEq]
        exact hsq'
      have hB : (40 / 47 + 2 * δ) / (1 + 2 * δ) < 102 / 109 := by
        have hd : 0 < 1 + 2 * δ := by linarith
        rw [div_lt_iff₀ hd]
        nlinarith [hδlt]
      have hBpos : 0 < (40 / 47 + 2 * δ) / (1 + 2 * δ) := by
        apply div_pos <;> linarith
      have hAB : (40 / 47 - δ) ^ 2 / (1 - δ) ^ 2 * ((40 / 47 + 2 * δ) / (1 + 2 * δ)) <
          100 / 289 * (102 / 109) := by
        have h1 := mul_lt_mul_of_pos_right hA hBpos
        have h2 := mul_lt_mul_of_pos_left hB (by norm_num : (0 : ℝ) < 100 / 289)
        linarith
      have hstep : (40 / 47 - δ) ^ 2 / (1 - δ) ^ 2 * ((40 / 47 + 2 * δ) / (1 + 2 * δ)) *
            ((57 : ℝ) / 50) * (28583 / 684) < (100 / 289 * (102 / 109)) * ((57 : ℝ) / 50) *
            (28583 / 684) := by
        have hk : 0 < ((57 : ℝ) / 50) * (28583 / 684) := by norm_num
        have h := mul_lt_mul_of_pos_right hAB hk
        nlinarith [h]
      have hnum2 : (100 / 289 * (102 / 109)) * ((57 : ℝ) / 50) * (28583 / 684) <
          (28583 / 684) - 25 := by norm_num
      linarith
  · -- tokens are not financeable
    intro hTok
    obtain ⟨t, ⟨ht0, ht1, htBE⟩, htuniq⟩ :=
      (TokenFinance.MoralHazard.contract_terms_exist 10 110 57 (by norm_num) (by norm_num)
        (by norm_num) hnpvpos).2
    set G : ℝ → ℝ := fun x => 10 / (10 + x) * (2 / (3 * 57)) * ((57 - 10) / 2 - x) ^ 3
      with hGdef
    have hcont : ContinuousOn (fun x : ℝ => 28583 / 684 - G x) (Set.Icc 5 6) := by
      apply ContinuousOn.sub continuousOn_const
      rw [hGdef]
      have hden : ContinuousOn (fun x : ℝ => 10 / (10 + x)) (Set.Icc 5 6) :=
        continuousOn_const.div (by fun_prop) (fun x hx => by
          have hx5 : (5 : ℝ) ≤ x := hx.1
          exact ne_of_gt (by linarith))
      exact (hden.mul continuousOn_const).mul (by fun_prop)
    have hF5 : 28583 / 684 - G 5 < 0 := by
      rw [hGdef]
      norm_num
    have hF6 : 0 < 28583 / 684 - G 6 := by
      rw [hGdef]
      norm_num
    obtain ⟨x, hxmem, hx0⟩ :=
      intermediate_value_Icc (by norm_num : (5 : ℝ) ≤ 6) hcont
        (Set.mem_Icc.mpr ⟨le_of_lt hF5, le_of_lt hF6⟩)
    have hxG : G x = 28583 / 684 := by linarith
    have hx5 : 5 < x := by
      rcases eq_or_lt_of_le hxmem.1 with h | h
      · exfalso
        rw [← h, hGdef] at hxG
        norm_num at hxG
      · exact h
    have hx6 : x < 6 := by
      rcases eq_or_lt_of_le hxmem.2 with h | h
      · exfalso
        rw [h, hGdef] at hxG
        norm_num at hxG
      · exact h
    have hxBE : TokenFinance.Debt.tokenBreakEven 10 110 57 x := by
      unfold TokenFinance.Debt.tokenBreakEven
      rw [htV]
      rw [hGdef] at hxG
      simpa using hxG
    have hxt : x = t := by
      refine htuniq x ⟨by linarith, ?_, hxBE⟩
      have h235 : (57 - 10 : ℝ) / 2 = 47 / 2 := by norm_num
      rw [h235]
      linarith
    have ht5 : 5 < t := by rw [← hxt]; exact hx5
    have ht6 : t < 6 := by rw [← hxt]; exact hx6
    obtain ⟨t', ht'0, ht'1, ht'BE', ht'eff⟩ := hTok
    have ht't : t' = t := htuniq t' ⟨ht'0, ht'1, ht'BE'⟩
    rw [ht't] at ht'eff
    set τ : ℝ := 2 * t / (57 - 10) with hτdef
    have hτ0 : 0 < τ := by
      rw [hτdef]
      exact div_pos (by linarith) (by norm_num)
    have hτ12 : τ < 12 / 47 := by
      rw [hτdef, div_lt_iff₀ (by norm_num : (0 : ℝ) < 57 - 10)]
      linarith
    have h7 := TokenFinance.MoralHazard.proposition_7 10 110 25 50 57 t τ (40 / 47) hMH
      ht0 ht1 htBE hτdef (by norm_num)
    have hcase : τ < 40 / 47 := by linarith only [hτ12]
    have h29 := (h7.2 hcase).mp ht'eff
    -- but (29) is false: its factor exceeds `64/125`, and `(64/125)(57/50)NPV_h > NPV_h - 25`
    have hbig := big_factor τ hτ12
    rw [hnpv57] at h29
    linarith only [h29, hbig]
  · -- equity is not financeable
    intro hEq
    have h5 := (TokenFinance.MoralHazard.proposition_5 10 110 25 50 57 (40 / 47) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hnpvpos (by norm_num)).mp hEq
    rw [hnpv57] at h5
    norm_num at h5
