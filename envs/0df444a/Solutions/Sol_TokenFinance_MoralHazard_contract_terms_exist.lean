-- Prove2me | solution 1 for TokenFinance.MoralHazard.contract_terms_exist
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-19T12:55:51.522173+00:00
-- url     : https://prove2.me/submissions/0546c73b-f7ac-43d9-8865-639ff2e19963

/-
DS19K proof of the MoralHazard milestone `TokenFinance.MoralHazard.contract_terms_exist`
(theorem_id 35b8a944-9403-4871-a647-c38afc67a88b): Appendix A, pp. 39-41, at `θ = θh`,
the break-even debt repayment `D` and the break-even token pre-sale `t` exist and are
unique.

Mathematics.  Write `L = θh − c > 0` and `A = L³/(12θh)`.

* Debt part.  `TokenFinance.Debt.proposition_2` (server Proved) already states, for
  `0 < c < θ`, `C₀ > 0`, `NPV > 0`, that there is exactly one `D ≥ 0` with
  `E_θ[min{πᵐ, D}] = C₀`.  We instantiate it at `θ = θh`; no re-proving is needed.

* Token part.  The break-even condition (16)/(26) reads
  `G(t) = A − C₀`, where `G(t) = c/(c+t) · 2/(3θh) · ((θh−c)/2 − t)³`.
  * `G(0) = A`, so `G(0) − (A − C₀) = C₀ > 0`.
  * `G(L/2) = 0`, so `G(L/2) − (A − C₀) = C₀ − A = −NPV_h < 0`, using `Debt.eq_3`
    (server Proved) which identifies `A − C₀` with `NPV_h`.
  * `G` is continuous on `[0, L/2]`, so the intermediate value theorem gives
    `t ∈ (0, L/2)` with `G(t) = A − C₀`; strict endpoint signs place `t` strictly
    inside.
  * Strict monotonicity:  on `(0, L/2)` both factors `c/(c+t)` and `(L/2 − t)³` are
    strictly positive and strictly decreasing in `t`, hence `G` is strictly decreasing:
    for `0 < s < t < L/2` we have `0 < L/2 − t < L/2 − s` and `0 < c + s < c + t`, so
    `(L/2−t)³ < (L/2−s)³` and `1/(c+t) < 1/(c+s)`, giving `G(t) < G(s)`.  A strictly
    decreasing function takes the value `A − C₀` at most once, which yields uniqueness.
-/
import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting
import Theorems.Thm_TokenFinance_Debt_proposition_2
import Theorems.Thm_TokenFinance_Debt_eq_3

theorem solution (c C0 θh : ℝ) (hc : 0 < c) (hcθ : c < θh) (hC0 : 0 < C0)
    (hnpv : 0 < TokenFinance.Debt.npv c C0 θh) :
    (∃! D : ℝ, 0 ≤ D ∧ TokenFinance.Debt.expect θh (TokenFinance.Debt.debtInv c D) = C0) ∧
    (∃! t : ℝ, 0 < t ∧ t < (θh - c) / 2 ∧ TokenFinance.Debt.tokenBreakEven c C0 θh t) := by
  have hθ : 0 < θh := lt_trans hc hcθ
  have hθne : θh ≠ 0 := ne_of_gt hθ
  have hcne : c ≠ 0 := ne_of_gt hc
  have hL : 0 < θh - c := by linarith
  -- (3), as a server-Proved platform lemma
  have hrhs : TokenFinance.Debt.npv c C0 θh = (θh - c) ^ 3 / (12 * θh) - C0 :=
    TokenFinance.Debt.eq_3 c C0 θh hc hcθ
  refine ⟨(TokenFinance.Debt.proposition_2 c C0 θh hc hcθ hC0 hnpv).1, ?_⟩
  -- the break-even left-hand side (16)
  set G : ℝ → ℝ :=
    fun t => c / (c + t) * (2 / (3 * θh)) * ((θh - c) / 2 - t) ^ 3 with hG
  have hG0 : G 0 = (θh - c) ^ 3 / (12 * θh) := by
    have h1 : c / (c + 0) = 1 := by
      rw [add_zero, div_self hcne]
    rw [hG]
    simp only [sub_zero]
    rw [h1, one_mul]
    field_simp
    ring
  have hGm : G ((θh - c) / 2) = 0 := by
    simp [hG]
  -- `G` is strictly decreasing on `(0, (θh - c)/2)`
  have hstrict : ∀ s t : ℝ, 0 < s → s < t → t < (θh - c) / 2 → G t < G s := by
    intro s t hs hst htm
    have hcs : 0 < c + s := by linarith
    have hle : c + s ≤ c + t := by linarith
    have hxt : 0 < (θh - c) / 2 - t := by linarith
    have hxs : 0 ≤ (θh - c) / 2 - s := by linarith
    have hlt : (θh - c) / 2 - t < (θh - c) / 2 - s := by linarith
    have hpow : ((θh - c) / 2 - t) ^ 3 < ((θh - c) / 2 - s) ^ 3 :=
      pow_lt_pow_left₀ hlt hxt.le (by norm_num)
    have hdiv : ((θh - c) / 2 - t) ^ 3 / (c + t) < ((θh - c) / 2 - s) ^ 3 / (c + s) :=
      div_lt_div₀ hpow hle (pow_nonneg hxs 3) hcs
    have hk : 0 < c * (2 / (3 * θh)) := by
      have h2 : 0 < 2 / (3 * θh) := by positivity
      exact mul_pos hc h2
    have hmul := mul_lt_mul_of_pos_left hdiv hk
    have hct : c + t ≠ 0 := ne_of_gt (by linarith)
    have e1 : G t = c * (2 / (3 * θh)) * (((θh - c) / 2 - t) ^ 3 / (c + t)) := by
      rw [hG]
      field_simp [hct]
    have e2 : G s = c * (2 / (3 * θh)) * (((θh - c) / 2 - s) ^ 3 / (c + s)) := by
      rw [hG]
      field_simp [ne_of_gt hcs]
    rw [e1, e2]
    exact hmul
  -- existence of `t` by the intermediate value theorem
  obtain ⟨t, ht0, htm, hbe⟩ : ∃ t : ℝ, 0 < t ∧ t < (θh - c) / 2 ∧
      TokenFinance.Debt.tokenBreakEven c C0 θh t := by
    have hm : 0 < (θh - c) / 2 := by linarith
    have hcontG : ContinuousOn G (Set.Icc 0 ((θh - c) / 2)) := by
      rw [hG]
      have h1 : ContinuousOn (fun t : ℝ => c / (c + t)) (Set.Icc 0 ((θh - c) / 2)) :=
        continuousOn_const.div (by fun_prop) (fun x hx => by
          have : 0 < c + x := by linarith [hx.1]
          exact ne_of_gt this)
      have h2 : ContinuousOn (fun t : ℝ => ((θh - c) / 2 - t) ^ 3)
          (Set.Icc 0 ((θh - c) / 2)) := by fun_prop
      exact (h1.mul continuousOn_const).mul h2
    have hcont : ContinuousOn (fun t : ℝ => TokenFinance.Debt.npv c C0 θh - G t)
        (Set.Icc 0 ((θh - c) / 2)) := continuousOn_const.sub hcontG
    have h0neg : TokenFinance.Debt.npv c C0 θh - G 0 < 0 := by
      rw [hG0, hrhs]
      linarith
    have hmpos : 0 < TokenFinance.Debt.npv c C0 θh - G ((θh - c) / 2) := by
      rw [hGm, sub_zero]
      exact hnpv
    have hmem : (0 : ℝ) ∈ Set.Icc (TokenFinance.Debt.npv c C0 θh - G 0)
        (TokenFinance.Debt.npv c C0 θh - G ((θh - c) / 2)) :=
      Set.mem_Icc.mpr ⟨le_of_lt h0neg, le_of_lt hmpos⟩
    obtain ⟨t, htmem, hteq⟩ :=
      intermediate_value_Icc (le_of_lt hm) hcont hmem
    have ht0 : 0 < t := by
      rcases eq_or_lt_of_le htmem.1 with h | h
      · exfalso
        rw [h.symm] at hteq
        linarith
      · exact h
    have htm : t < (θh - c) / 2 := by
      rcases eq_or_lt_of_le htmem.2 with h | h
      · exfalso
        rw [h] at hteq
        linarith
      · exact h
    refine ⟨t, ht0, htm, ?_⟩
    have hGt : G t = TokenFinance.Debt.npv c C0 θh := by
      have h' : TokenFinance.Debt.npv c C0 θh - G t = 0 := hteq
      linarith
    show c / (c + t) * (2 / (3 * θh)) * ((θh - c) / 2 - t) ^ 3
        = (θh - c) ^ 3 / (12 * θh) - C0
    rw [← hrhs]
    exact hGt
  refine ⟨t, ⟨ht0, htm, hbe⟩, ?_⟩
  intro u hu
  obtain ⟨hu0, hum, hbeu⟩ := hu
  rw [TokenFinance.Debt.tokenBreakEven] at hbe hbeu
  rcases lt_trichotomy u t with h | h | h
  · have hthis := hstrict u t hu0 h htm
    rw [hG] at hthis
    simp only at hthis
    linarith
  · exact h
  · have hthis := hstrict t u ht0 h hum
    rw [hG] at hthis
    simp only at hthis
    linarith
