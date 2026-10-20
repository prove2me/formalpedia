-- Prove2me | solution 1 for TokenFinance.MoralHazard.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T14:11:53.799101+00:00
-- url     : https://prove2.me/submissions/cbd86670-0074-48d8-a103-c1e44091f99f

/-
DS19P root assembly for `TokenFinance.MoralHazard.proposition_8`
(theorem_id c546d25f-0946-4383-9058-457324526441), mission 927c6e6b-1073-410d-b167-351eb841e6ca.

Proposition 8 (p. 34) is the four-clause statement

  1. equity   ⊆ token  : `EquityFinanceable → TokenFinanceable`
  2. token    ⊆ debt   : `TokenFinanceable → DebtFinanceable`
  3. strictness        : some admissible project is token-financeable but not equity-financeable
  4. strictness        : some admissible project is debt-financeable but not token-financeable

Clauses 1 and 3 are exactly the two conjuncts of the accepted milestone `corollary_3`
(Equity ⊆ Token, converse false). Clause 4 reuses the standing assumptions, debt financeability
and token non-financeability from `appendixB_theta57`, which exhibits
the Appendix B parameters `c = 10, C₀ = 110, θl = 50, θh = 57, C_e = 25` where debt succeeds and
tokens fail.  Clause 2 is NOT implied by corollaries 2–3 (they prove `Equity ⊆ Debt` and
`Equity ⊆ Token`, which leave `Token ⊆ Debt` open); it is proved here from the source with the
contract-term ordering.

`token_to_debt`, below, is the actual new content of this file: the missing inclusion.
Let `λ = (θl−c)/(θh−c) ∈ (0,1)`, let `t` be a break-even token pre-sale supplied by
`TokenFinanceable`, and let `D ≥ 0` be the break-even debt face value of (21), which exists by
`contract_terms_exist` (Proved).  Put `τ = 2t/(θh−c)` and `δ = 2√D/(θh−c)`.

* If `λ ≤ δ`, Proposition 6 (Proved) yields debt financeability directly.
* If `δ < λ`, Lemma 6 (Proved) gives `τ < δ² < δ < λ`, so `τ < λ`, and Proposition 7 (Proved)
  converts the token effort inequality into `NPV_h − C_e ≥ (λ−τ)³/(1−τ)³ · (θh/θl) · NPV_h`
  (29).  Lemma 7 (Proved) supplies
  `(λ−τ)³/(1−τ)³ > (λ−δ)²/(1−δ)² · (λ+2δ)/(1+2δ)`; multiplying by `(θh/θl)NPV_h > 0` gives the
  debt incentive constraint (24), and Proposition 6 then produces the witnessing repayment `D`.

This is the source's ordering "debt is best at mitigating moral hazard, tokens second, equity
worst" used at the level of the incentive factors (24), (29), (20), with the direction supplied
by Lemma 7 rather than assumed.

The final upload does not import any `Solutions.*` module (local helpers during development
only). The now-Proved milestones `corollary_3` and `appendixB_theta57` are imported as
ordinary platform theorems; their live Proved status was independently verified before approval.
-/
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Definitions.Def_TokenFinance_MoralHazard_Financeable
import Theorems.Thm_TokenFinance_MoralHazard_contract_terms_exist
import Theorems.Thm_TokenFinance_MoralHazard_proposition_6
import Theorems.Thm_TokenFinance_MoralHazard_proposition_7
import Theorems.Thm_TokenFinance_MoralHazard_lemma_6
import Theorems.Thm_TokenFinance_MoralHazard_lemma_7
import Theorems.Thm_TokenFinance_MoralHazard_corollary_3
import Theorems.Thm_TokenFinance_MoralHazard_appendixB_theta57

open TokenFinance.MoralHazard

/-- The missing inclusion of Proposition 8: under the standing assumptions, every project that
can be financed by the optimal token contract can also be financed by debt. -/
private theorem token_to_debt :
    ∀ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh →
      TokenFinanceable c C0 Ce θl θh → DebtFinanceable c C0 Ce θl θh := by
  intro c C0 Ce θl θh hA hTok
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
  obtain ⟨t, ht0, ht1, htBE, hint⟩ := hTok
  obtain ⟨D, ⟨hD0, hDBE⟩, -⟩ :=
    (TokenFinance.MoralHazard.contract_terms_exist c C0 θh hc hcθh hC0 hnpvh).1
  set δ : ℝ := 2 * Real.sqrt D / (θh - c) with hδdef
  set τ : ℝ := 2 * t / (θh - c) with hτdef
  obtain ⟨hτ0, hτδ2, hδ21, hδ1⟩ :=
    TokenFinance.MoralHazard.lemma_6 c C0 θh D t δ τ hc hcθh hC0 hnpvh hD0 hDBE ht0 ht1
      htBE hδdef hτdef
  have h6 := TokenFinance.MoralHazard.proposition_6 c C0 Ce θl θh D δ lam hAkeep hD0 hDBE
    hδdef hlamdef
  have h7 := TokenFinance.MoralHazard.proposition_7 c C0 Ce θl θh t τ lam hAkeep ht0 ht1
    htBE hτdef hlamdef
  by_cases hcase : lam ≤ δ
  · exact (h6.1 hcase).2
  · push Not at hcase
    have hτlam : τ < lam := lt_trans (lt_trans hτδ2 hδ21) hcase
    refine ⟨D, hD0, hDBE, ?_⟩
    refine (h6.2 hcase).mpr ?_
    have h29 := (h7.2 hτlam).mp hint
    have h7l := TokenFinance.MoralHazard.lemma_7 c C0 θh D t δ τ lam hc hcθh hC0 hnpvh
      hD0 hDBE ht0 ht1 htBE hδdef hτdef hcase hlam1
    have hK : 0 < (θh / θl) * TokenFinance.Debt.npv c C0 θh :=
      mul_pos (div_pos hθh hθl) hnpvh
    have hmul := mul_lt_mul_of_pos_right h7l.2 hK
    nlinarith [hmul, h29]

/-- Proposition 8 (p. 34): under moral hazard, every project that can be financed by equity can
be financed by the optimal token contract, and every project that can be financed by tokens can
be financed by debt; both inclusions are strict. -/
theorem solution :
    (∀ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh →
      EquityFinanceable c C0 Ce θl θh → TokenFinanceable c C0 Ce θl θh) ∧
    (∀ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh →
      TokenFinanceable c C0 Ce θl θh → DebtFinanceable c C0 Ce θl θh) ∧
    (∃ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh ∧
      TokenFinanceable c C0 Ce θl θh ∧ ¬ EquityFinanceable c C0 Ce θl θh) ∧
    (∃ c C0 Ce θl θh : ℝ, MHAssumptions c C0 Ce θl θh ∧
      DebtFinanceable c C0 Ce θl θh ∧ ¬ TokenFinanceable c C0 Ce θl θh) := by
  obtain ⟨hInc, hStrict⟩ := TokenFinance.MoralHazard.corollary_3
  obtain ⟨h57MH, h57D, h57nT, -⟩ := TokenFinance.MoralHazard.appendixB_theta57
  exact ⟨hInc, token_to_debt, hStrict, ⟨10, 110, 25, 50, 57, h57MH, h57D, h57nT⟩⟩
