-- Prove2me | solution 1 for TechSourcing.PTS.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T03:29:44.949579+00:00
-- url     : https://prove2.me/submissions/c1a0fbeb-b48b-4a72-ac75-12268d1f73fc

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model
import Theorems.Thm_TechSourcing_PTS_lemma_1_equity
import Theorems.Thm_TechSourcing_PTS_lemma_1_loan
import Theorems.Thm_TechSourcing_PTS_lemma_1_equity_denominator
import Theorems.Thm_TechSourcing_PTS_comparison
import Theorems.Thm_TechSourcing_PTS_monotone_convex

open TechSourcing.PTS

/-- At a pair of equilibria with `θ < 1`, equity wins iff `F > 0`. -/
private lemma key (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P)
    (oE : EqOutcome) (φE : ℝ) (oL : LoanOutcome) (φL : ℝ)
    (hE : IsEquityEq P oE φE) (hE1 : oE.θ < 1)
    (hL : IsLoanEq P oL φL) (hL1 : oL.θ < 1) :
    (oL.θ < oE.θ ↔ 0 < Fcmp P) := by
  have eE := ((lemma_1_equity P hP hWL).1 oE φE hE hE1).1
  have eL := ((lemma_1_loan P hP hWL).1 oL φL hL hL1).1
  have hden := lemma_1_equity_denominator P hP hWL oE φE hE hE1
  have hE0 : 0 < thetaEStar P := by
    unfold thetaEStar; exact div_pos (by linarith) (by linarith)
  have hL0 : 0 ≤ oL.θ := ((isLoanEq_iff P oL φL).1 hL).1.1.2.2.1.1
  have hL0' : 0 < thetaLStar P := by
    have ha := hP.1
    unfold thetaLStar
    set X := 1 + 3 * P.a / P.b - P.a / 2 * Lb P
    have h6 : 0 < 6 * P.a * (Wb P - Lb P) := by
      have : 0 < Wb P - Lb P := by linarith
      positivity
    have : X < Real.sqrt (X ^ 2 + 6 * P.a * (Wb P - Lb P)) := by
      rcases lt_or_ge X 0 with hX | hX
      · exact lt_of_lt_of_le hX (Real.sqrt_nonneg _)
      · rw [show X = Real.sqrt (X ^ 2) from (Real.sqrt_sq hX).symm]
        rw [Real.sqrt_sq hX]
        exact Real.lt_sqrt hX |>.2 (by linarith)
    linarith
  rw [eE, eL]
  exact (comparison P hP hWL hE0 (eE ▸ hE1) hL0' (eL ▸ hL1)).2

theorem solution :
    (∀ P : Params, P.Standing → Lb P < Wb P →
      (∃ aT : ℝ, ∀ a : ℝ, 0 < a → ∀ (oE : EqOutcome) (φE : ℝ) (oL : LoanOutcome) (φL : ℝ),
          IsEquityEq { P with a := a } oE φE → oE.θ < 1 →
          IsLoanEq { P with a := a } oL φL → oL.θ < 1 →
          (oL.θ < oE.θ ↔ aT < a)) ∨
      (∀ a : ℝ, 0 < a → ∀ (oE : EqOutcome) (φE : ℝ) (oL : LoanOutcome) (φL : ℝ),
          IsEquityEq { P with a := a } oE φE → oE.θ < 1 →
          IsLoanEq { P with a := a } oL φL → oL.θ < 1 → oE.θ ≤ oL.θ)) ∧
    (∀ P : Params, P.Standing →
      ∃ βL βH : ℝ, βL ≤ βH ∧ ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
        Lb { P with β := β } < Wb { P with β := β } →
        ∀ (oE : EqOutcome) (φE : ℝ) (oL : LoanOutcome) (φL : ℝ),
          IsEquityEq { P with β := β } oE φE → oE.θ < 1 →
          IsLoanEq { P with β := β } oL φL → oL.θ < 1 →
          (oL.θ < oE.θ ↔ β < βL ∨ βH < β)) := by
  refine ⟨fun P hP hWL => ?_, fun P hP => ?_⟩
  · obtain ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ := hP
    have hPa : ∀ a : ℝ, 0 < a → ({ P with a := a } : Params).Standing :=
      fun a h => ⟨h, hb, hc, hD, hR, hβ0, hβ1⟩
    have hWLa : ∀ a : ℝ, Lb { P with a := a } < Wb { P with a := a } := fun a => hWL
    set F : ℝ → ℝ := fun a => Fcmp { P with a := a } with hFdef
    have hmono : StrictMonoOn F (Set.Ioi 0) :=
      (monotone_convex P ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩).2.1
    have hcont : ∀ a : ℝ, 0 < a → ContinuousAt F a := by
      intro a h
      simp only [hFdef, Fcmp, Wb, Lb, gammaHat, TechSourcing.PTS.sq]
      have h1 : a ≠ 0 := h.ne'
      have h2 : P.b ≠ 0 := hb.ne'
      fun_prop (disch := first | assumption | positivity | (exact mul_ne_zero h1 h2) | (exact pow_ne_zero 2 h1) | (exact pow_ne_zero 2 h2) | (exact mul_ne_zero (by norm_num) h2) | (exact mul_ne_zero (by norm_num) h1))
    by_cases hS : ∃ a, 0 < a ∧ 0 < F a
    · left
      set S := {a : ℝ | 0 < a ∧ 0 < F a}
      have hSne : S.Nonempty := hS
      have hSbdd : BddBelow S := ⟨0, fun x hx => hx.1.le⟩
      refine ⟨sInf S, fun a ha' oE φE oL φL hE hE1 hL hL1 => ?_⟩
      rw [key _ (hPa a ha') (hWLa a) oE φE oL φL hE hE1 hL hL1]
      change 0 < F a ↔ _
      constructor
      · intro hFa
        have hmem : a ∈ S := ⟨ha', hFa⟩
        have hev : ∀ᶠ x in nhds a, 0 < F x := continuousAt_const.eventually_lt (hcont a ha') hFa
        obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
        set a' := max (a / 2) (a - ε / 2)
        have ha'pos : 0 < a' := lt_max_of_lt_left (by linarith)
        have ha'lt : a' < a := max_lt (by linarith) (by linarith)
        have hdist : dist a' a < ε := by
          rw [Real.dist_eq, abs_lt]; constructor
          · have : a - ε / 2 ≤ a' := le_max_right _ _
            linarith
          · linarith
        have : a' ∈ S := ⟨ha'pos, hball hdist⟩
        exact lt_of_le_of_lt (csInf_le hSbdd this) ha'lt
      · intro hlt
        obtain ⟨s, hs, hsa⟩ := exists_lt_of_csInf_lt hSne hlt
        exact lt_trans hs.2 (hmono hs.1 (show (0:ℝ) < a from ha') hsa)
    · right
      intro a ha' oE φE oL φL hE hE1 hL hL1
      have := key _ (hPa a ha') (hWLa a) oE φE oL φL hE hE1 hL hL1
      by_contra hcon
      push Not at hcon
      exact hS ⟨a, ha', this.1 hcon⟩
  · obtain ⟨q₂, q₁, q₀, hq₂, hq⟩ := (monotone_convex P hP).2.2
    obtain ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ := hP
    have hPb : ∀ β : ℝ, 0 ≤ β → β ≤ 1 → ({ P with β := β } : Params).Standing :=
      fun β h0 h1 => ⟨ha, hb, hc, hD, hR, h0, h1⟩
    set disc := q₁ ^ 2 - 4 * q₂ * q₀
    by_cases hd : 0 ≤ disc
    · refine ⟨(-q₁ - Real.sqrt disc) / (2 * q₂), (-q₁ + Real.sqrt disc) / (2 * q₂), ?_, ?_⟩
      · apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [Real.sqrt_nonneg disc]
      intro β h0 h1 hWL oE φE oL φL hE hE1 hL hL1
      rw [key _ (hPb β h0 h1) hWL oE φE oL φL hE hE1 hL hL1, hq β]
      have hs : Real.sqrt disc ^ 2 = disc := Real.sq_sqrt hd
      have hfac : q₂ * β ^ 2 + q₁ * β + q₀ =
          q₂ * (β - (-q₁ - Real.sqrt disc) / (2 * q₂)) * (β - (-q₁ + Real.sqrt disc) / (2 * q₂)) := by
        field_simp
        nlinarith [hs]
      rw [hfac]
      have hle : (-q₁ - Real.sqrt disc) / (2 * q₂) ≤ (-q₁ + Real.sqrt disc) / (2 * q₂) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [Real.sqrt_nonneg disc]
      set u := (-q₁ - Real.sqrt disc) / (2 * q₂)
      set v := (-q₁ + Real.sqrt disc) / (2 * q₂)
      constructor
      · intro hpos
        have : 0 < (β - u) * (β - v) := by
          rw [mul_assoc] at hpos; exact pos_of_mul_pos_right hpos hq₂.le
        rcases lt_or_ge β u with h | h
        · exact Or.inl h
        · right
          by_contra hv; push Not at hv
          have : (β - u) * (β - v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          linarith
      · rintro (h | h)
        · have : 0 < (β - u) * (β - v) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
          rw [mul_assoc]; positivity
        · have : 0 < (β - u) * (β - v) := mul_pos (by linarith) (by linarith)
          rw [mul_assoc]; positivity
    · refine ⟨2, 2, le_rfl, ?_⟩
      intro β h0 h1 hWL oE φE oL φL hE hE1 hL hL1
      rw [key _ (hPb β h0 h1) hWL oE φE oL φL hE hE1 hL hL1, hq β]
      push Not at hd
      constructor
      · intro _; left; linarith
      · intro _
        have : q₂ * β ^ 2 + q₁ * β + q₀ = q₂ * (β + q₁ / (2 * q₂)) ^ 2 - disc / (4 * q₂) := by
          field_simp; ring
        rw [this]
        have : 0 < - disc / (4 * q₂) := div_pos (by linarith) (by positivity)
        have : 0 ≤ q₂ * (β + q₁ / (2 * q₂)) ^ 2 := by positivity
        rw [sub_eq_add_neg, ← neg_div]; linarith
