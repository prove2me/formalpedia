-- Prove2me | solution 1 for TokenFinance.MoralHazard.corollary_3
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T13:49:10.808034+00:00
-- url     : https://prove2.me/submissions/0cc6fec6-1afd-4dda-bd63-45ae49c0229b

/-
DS19M proof of the MoralHazard milestone `TokenFinance.MoralHazard.corollary_3`
(theorem_id 103f299d-1b6d-469e-bb06-a70b07b476c7): Corollary 3, p. 33 — every project
financeable by equity under moral hazard is financeable by the optimal token contract, and
the converse fails.

Mathematics.  Let `λ = (θl−c)/(θh−c) ∈ (0,1)`.

* Inclusion.  Proposition 5 (Proved) turns `EquityFinanceable` into
  `NPV_h − C_e ≥ λ³(θh/θl)NPV_h`.  Let `t` be the break-even pre-sale of (16), which exists by
  contract_terms_exist (Proved), and put `τ = 2t/(θh−c) ∈ (0,1)`.  If `λ ≤ τ`, Proposition 7
  (Proved) gives token financeability directly.  If `τ < λ`, Lemma 5 (Proved) gives
  `λ³ > (λ−τ)³/(1−τ)³`; multiplying by `(θh/θl)NPV_h > 0` and combining with the equity
  inequality yields the token incentive constraint (29), and Proposition 7 then produces the
  witnessing pre-sale `t`.

* Strictness.  For `C₀ = 110`, `c = 10`, `θl = 50`, `θh = 60`, `C_e = 25` the token contract is
  financeable while equity is not.  The standing assumptions hold
  (`NPV_h = 1145/18 > 25`, `NPV_l = −10/3 ≤ 0`).  Equity fails because
  `NPV_h − C_e = 695/18 < (4/5)³(6/5)(1145/18) = 439680/11250` (Proposition 5).  For tokens,
  the break-even left side `G` of (16) is continuous with
  `G(4) = 147/2 > 1145/18 > 1600/27 = G(5)`, so `G` attains `1145/18` at some `x ∈ (4,5)`;
  uniqueness of the break-even pre-sale gives `x = t`, hence `4 < t < 5` and
  `4/25 < τ < 1/5`.  With `τ > 4/25` the factor `((λ−τ)/(1−τ))³` of (29) is below
  `(16/21)³ = 4096/9261`, and `(4096/9261)(6/5)(1145/18) < 695/18`, so Proposition 7 yields
  `TokenFinanceable`.

No rounded numerical root is used: the bracket for `t` is an exactly proved interval.
-/
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable
import Theorems.Thm_TokenFinance_Debt_eq_3
import Theorems.Thm_TokenFinance_MoralHazard_contract_terms_exist
import Theorems.Thm_TokenFinance_MoralHazard_proposition_5
import Theorems.Thm_TokenFinance_MoralHazard_proposition_7
import Theorems.Thm_TokenFinance_MoralHazard_lemma_5

open TokenFinance.MoralHazard

theorem solution :
    (∀ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh →
      EquityFinanceable c C0 Ce θl θh → TokenFinanceable c C0 Ce θl θh) ∧
    (∃ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh ∧
      TokenFinanceable c C0 Ce θl θh ∧ ¬ EquityFinanceable c C0 Ce θl θh) := by
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
    obtain ⟨t, ⟨ht0, ht1, htBE⟩, -⟩ :=
      (TokenFinance.MoralHazard.contract_terms_exist c C0 θh hc hcθh hC0 hnpvh).2
    set τ : ℝ := 2 * t / (θh - c) with hτdef
    have hτpos : 0 < τ := by
      rw [hτdef]
      exact div_pos (by linarith) hL
    have hτ1 : τ < 1 := by
      rw [hτdef, div_lt_one hL]
      linarith
    have h7 := TokenFinance.MoralHazard.proposition_7 c C0 Ce θl θh t τ lam hAkeep ht0 ht1
      htBE hτdef hlamdef
    by_cases hcase : lam ≤ τ
    · exact (h7.1 hcase).2
    · push_neg at hcase
      refine ⟨t, ht0, ht1, htBE, (h7.2 hcase).mpr ?_⟩
      have h5l := TokenFinance.MoralHazard.lemma_5 τ lam hτpos hcase hlam1
      have hK : 0 < (θh / θl) * TokenFinance.Debt.npv c C0 θh :=
        mul_pos (div_pos hθh hθl) hnpvh
      have hmul := mul_lt_mul_of_pos_right h5l hK
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
    · obtain ⟨t, ⟨ht0, ht1, htBE⟩, htuniq⟩ :=
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
      set τ : ℝ := 2 * t / (60 - 10) with hτdef
      have hτ4 : 4 / 25 < τ := by
        rw [hτdef]
        rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 60 - 10)]
        linarith
      have hτ5 : τ < 4 / 5 := by
        rw [hτdef, div_lt_iff₀ (by norm_num : (0 : ℝ) < 60 - 10)]
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
    · intro hEq
      have h5 := (TokenFinance.MoralHazard.proposition_5 10 110 25 50 60 (4 / 5) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) hnpvpos (by norm_num)).mp hEq
      rw [hnpv60] at h5
      norm_num at h5
