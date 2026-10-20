-- Prove2me | solution 1 for TokenFinance.MoralHazard.appendixB_theta60
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T13:48:59.063014+00:00
-- url     : https://prove2.me/submissions/e07ff421-106a-4557-82c2-186cb194279f

/-
DS19M proof of the MoralHazard milestone `TokenFinance.MoralHazard.appendixB_theta60`
(theorem_id a08ed45d-68d0-4c90-81b9-9addda5f1ace): Appendix B, pp. 45-47, the instance
`C₀ = 110`, `c = 10`, `θl = 50`, `θh = 60`, `C_e = 25`.

Mathematics.  The standing assumptions hold because
`NPV_h = (θh−c)³/(12θh) − C₀ = 1145/18 > 25` and `NPV_l = −10/3 ≤ 0` (both from (3)).

* Equity fails.  Proposition 5 (Proved) rewrites equity financeability as
  `NPV_h − C_e ≥ λ³(θh/θl)NPV_h` with `λ = 4/5`; the left side is `695/18` while the right
  side is `(64/125)(6/5)(1145/18) = 439680/11250`, and `695·11250 < 439680·18`.

* Debt succeeds.  The break-even repayment `D` of (21) exists (contract_terms_exist, Proved)
  and satisfies `D < (θh−c)²/4`, so `δ = 2√D/(θh−c) ∈ (0,1)`.  Equation (48) turns the
  break-even identity into the exact cubic relation `1250δ³ − 1875δ² + 396 = 0`; the cubic is
  strictly decreasing on `(0,1)` and changes sign between `29/50` and `3/5`, hence
  `29/50 < δ < 3/5`.  Then Proposition 6 (Proved) gives debt financeability once the
  incentive constraint (24) is checked: the factor
  `((λ−δ)/(1−δ))²` is below `(11/21)²` (because `δ > 29/50`) and `(λ+2δ)/(1+2δ)` is below
  `10/11` (because `δ < 3/5` and `λ < 1`), so the whole right side is below
  `(110/441)(6/5)(1145/18) < 695/18 = NPV_h − C_e`.

* Tokens succeed.  The break-even pre-sale `t` of (16) exists (contract_terms_exist, Proved).
  Writing `G(t)` for the left side of (16), `G` is continuous,
  `G(4) = 147/2 > 1145/18 > 1600/27 = G(5)`, so the value `1145/18` is attained at some
  `x ∈ (4,5)`; by the uniqueness clause of contract_terms_exist, `x = t`, so `4 < t < 5` and
  `τ = 2t/(θh−c) ∈ (4/25, 1/5)`.  Proposition 7 (Proved) then gives token financeability:
  for `τ < λ` the factor `((λ−τ)/(1−τ))³` is below `(16/21)³ = 4096/9261` and
  `(4096/9261)(6/5)(1145/18) < 695/18`.

The file imports only Mathlib, the two platform definition modules, and server-Proved
platform theorems; every numerical bound is proved exactly, no rounded root is used.
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
    MHAssumptions 10 110 25 50 60 ∧ TokenFinanceable 10 110 25 50 60 ∧
      DebtFinanceable 10 110 25 50 60 ∧ ¬ EquityFinanceable 10 110 25 50 60 := by
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
  refine ⟨hMH, ?_, ?_, ?_⟩
  · -- the break-even pre-sale `t` exists and lies in `(4,5)`
    obtain ⟨t, ⟨ht0, ht1, htBE⟩, htuniq⟩ :=
      (TokenFinance.MoralHazard.contract_terms_exist 10 110 60 (by norm_num) (by norm_num)
        (by norm_num) hnpvpos).2
    have htV : (60 - 10 : ℝ) ^ 3 / (12 * 60) - 110 = 1145 / 18 := by norm_num
    set G : ℝ → ℝ := fun x => 10 / (10 + x) * (2 / (3 * 60)) * ((60 - 10) / 2 - x) ^ 3
      with hGdef
    have hcont : ContinuousOn (fun x : ℝ => 1145 / 18 - G x) (Set.Icc 4 5) := by
      apply ContinuousOn.sub continuousOn_const
      rw [hGdef]
      have hden : ContinuousOn (fun x : ℝ => 10 / (10 + x)) (Set.Icc 4 5) :=
        continuousOn_const.div (by fun_prop) (fun x hx => by
          have hx4 : (4 : ℝ) ≤ x := hx.1
          exact ne_of_gt (by linarith))
      exact (hden.mul continuousOn_const).mul (by fun_prop)
    have hF4 : 1145 / 18 - G 4 < 0 := by
      rw [hGdef]
      norm_num
    have hF5 : 0 < 1145 / 18 - G 5 := by
      rw [hGdef]
      norm_num
    obtain ⟨x, hxmem, hx0⟩ :=
      intermediate_value_Icc (by norm_num : (4 : ℝ) ≤ 5) hcont
        (Set.mem_Icc.mpr ⟨le_of_lt hF4, le_of_lt hF5⟩)
    have hxG : G x = 1145 / 18 := by linarith
    have hx4 : 4 < x := by
      rcases eq_or_lt_of_le hxmem.1 with h | h
      · exfalso
        rw [← h, hGdef] at hxG
        norm_num at hxG
      · exact h
    have hx5 : x < 5 := by
      rcases eq_or_lt_of_le hxmem.2 with h | h
      · exfalso
        rw [h, hGdef] at hxG
        norm_num at hxG
      · exact h
    have hxBE : TokenFinance.Debt.tokenBreakEven 10 110 60 x := by
      unfold TokenFinance.Debt.tokenBreakEven
      rw [htV]
      rw [hGdef] at hxG
      simpa using hxG
    have hxt : x = t := by
      refine htuniq x ⟨by linarith, ?_, hxBE⟩
      have h25 : (60 - 10 : ℝ) / 2 = 25 := by norm_num
      rw [h25]
      linarith
    have ht4 : 4 < t := by rw [← hxt]; exact hx4
    have ht5 : t < 5 := by rw [← hxt]; exact hx5
    -- `τ = 2t/(θh−c)`
    set τ : ℝ := 2 * t / (60 - 10) with hτdef
    have hτ4 : 4 / 25 < τ := by
      rw [hτdef]
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 60 - 10)]
      linarith
    have hτ5 : τ < 4 / 5 := by
      rw [hτdef]
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 60 - 10)]
      linarith
    have h7 := TokenFinance.MoralHazard.proposition_7 10 110 25 50 60 t τ (4 / 5) hMH
      ht0 ht1 htBE hτdef (by norm_num)
    have hfin : TokenFinance.Debt.expect 60
          (fun x => TokenFinance.Debt.tokEnt 10 t x (TokenFinance.Debt.qm 10 x)) - 25 ≥
        TokenFinance.Debt.expect 50
          (fun x => TokenFinance.Debt.tokEnt 10 t x (TokenFinance.Debt.qm 10 x)) := by
      by_cases hcase : (4 / 5 : ℝ) ≤ τ
      · exact (h7.1 hcase).1
      · push_neg at hcase
        refine (h7.2 hcase).mpr ?_
        rw [hnpv60]
        have hden : 0 < 1 - τ := by linarith
        have hnum : 0 < 4 / 5 - τ := by linarith
        have hratio : (4 / 5 - τ) / (1 - τ) < 16 / 21 := by
          rw [div_lt_iff₀ hden]
          nlinarith [hτ4]
        have hcube : ((4 / 5 - τ) / (1 - τ)) ^ 3 < (16 / 21) ^ 3 :=
          pow_lt_pow_left₀ hratio (le_of_lt (div_pos hnum hden)) (by norm_num)
        have hcube' : ((4 / 5 - τ) / (1 - τ)) ^ 3 < 4096 / 9261 := by
          have hval : (16 / 21 : ℝ) ^ 3 = 4096 / 9261 := by norm_num
          linarith
        have hEq : (4 / 5 - τ) ^ 3 / (1 - τ) ^ 3 = ((4 / 5 - τ) / (1 - τ)) ^ 3 := by
          rw [div_pow]
        rw [hEq]
        have hstep : ((4 / 5 - τ) / (1 - τ)) ^ 3 * ((60 : ℝ) / 50) * (1145 / 18) <
            (4096 / 9261) * ((60 : ℝ) / 50) * (1145 / 18) := by
          have hk : 0 < ((60 : ℝ) / 50) * (1145 / 18) := by norm_num
          have h := mul_lt_mul_of_pos_right hcube' hk
          nlinarith [h]
        have hnum2 : (4096 / 9261) * ((60 : ℝ) / 50) * (1145 / 18) < (1145 / 18) - 25 := by
          norm_num
        linarith
    exact ⟨t, ht0, ht1, htBE, hfin⟩
  · -- debt financeability via the break-even repayment and Proposition 6
    obtain ⟨D, ⟨hD0, hDBE⟩, -⟩ :=
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
    have hδ0 : 0 ≤ δ := by
      rw [hδdef]
      positivity
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
  · -- equity is not financeable
    intro hEq
    have h5 := (TokenFinance.MoralHazard.proposition_5 10 110 25 50 60 (4 / 5) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hnpvpos (by norm_num)).mp hEq
    rw [hnpv60] at h5
    norm_num at h5
