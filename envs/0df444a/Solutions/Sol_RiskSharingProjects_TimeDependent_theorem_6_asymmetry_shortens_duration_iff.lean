-- Prove2me | solution 1 for RiskSharingProjects.TimeDependent.theorem_6_asymmetry_shortens_duration_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T23:43:17.378724+00:00
-- url     : https://prove2.me/submissions/c26064d3-55b9-4b55-b29d-a8fd2584ad8f

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_SupplierBelief
import Definitions.Def_RiskSharingProjects_TimeDependent_qLow
import Definitions.Def_RiskSharingProjects_TimeDependent_qHigh
import Definitions.Def_RiskSharingProjects_TimeDependent_AsymmetryShortensDuration
import Definitions.Def_RiskSharingProjects_TimeDependent_Condition2

set_option autoImplicit false

namespace RSPT6

open RiskSharingProjects.TimeDependent MeasureTheory

lemma dp0 (a b : ℝ) : delayPenalty a b 0 = 0 := rfl
lemma dp1 (a b : ℝ) : delayPenalty a b 1 = a := rfl
lemma dp2 (a b : ℝ) : delayPenalty a b 2 = a + b := rfl

lemma pd_kk : projectDelay Action.keep Action.keep = 0 := by decide
lemma pd_kd : projectDelay Action.keep Action.delay = 1 := by decide
lemma pd_dk : projectDelay Action.delay Action.keep = 1 := by decide
lemma pd_dd : projectDelay Action.delay Action.delay = 2 := by decide

section payoffs
variable (s p q : ℝ)

lemma sp_kk : supplierPayoff s p q Action.keep Action.keep = 0 := by
  unfold supplierPayoff; rw [pd_kk, dp0]; simp
lemma sp_kd : supplierPayoff s p q Action.keep Action.delay = -p := by
  unfold supplierPayoff; rw [pd_kd, dp1]; simp
lemma sp_dk : supplierPayoff s p q Action.delay Action.keep = s - p := by
  unfold supplierPayoff; rw [pd_dk, dp1]; simp
lemma sp_dd : supplierPayoff s p q Action.delay Action.delay = s - (p + q) := by
  unfold supplierPayoff; rw [pd_dd, dp2]; simp

lemma mp_kk : manufacturerPayoff s p q Action.keep Action.keep = 0 := by
  unfold manufacturerPayoff; rw [pd_kk, dp0]; simp
lemma mp_kd : manufacturerPayoff s p q Action.keep Action.delay = s - p := by
  unfold manufacturerPayoff; rw [pd_kd, dp1]; simp
lemma mp_dk : manufacturerPayoff s p q Action.delay Action.keep = -p := by
  unfold manufacturerPayoff; rw [pd_dk, dp1]; simp
lemma mp_dd : manufacturerPayoff s p q Action.delay Action.delay = s - (p + q) := by
  unfold manufacturerPayoff; rw [pd_dd, dp2]; simp

lemma br_kk : Action.keep ∈ manufacturerBestResponses s p q Action.keep ↔ s ≤ p := by
  simp only [manufacturerBestResponses, Set.mem_setOf_eq]
  constructor
  · intro h; have := h Action.delay; rw [mp_kd, mp_kk] at this; linarith
  · intro h b; cases b <;> simp only [mp_kk, mp_kd] <;> linarith
lemma br_kd : Action.delay ∈ manufacturerBestResponses s p q Action.keep ↔ p ≤ s := by
  simp only [manufacturerBestResponses, Set.mem_setOf_eq]
  constructor
  · intro h; have := h Action.keep; rw [mp_kd, mp_kk] at this; linarith
  · intro h b; cases b <;> simp only [mp_kk, mp_kd] <;> linarith
lemma br_dk : Action.keep ∈ manufacturerBestResponses s p q Action.delay ↔ s ≤ q := by
  simp only [manufacturerBestResponses, Set.mem_setOf_eq]
  constructor
  · intro h; have := h Action.delay; rw [mp_dd, mp_dk] at this; linarith
  · intro h b; cases b <;> simp only [mp_dk, mp_dd] <;> linarith
lemma br_dd : Action.delay ∈ manufacturerBestResponses s p q Action.delay ↔ q ≤ s := by
  simp only [manufacturerBestResponses, Set.mem_setOf_eq]
  constructor
  · intro h; have := h Action.keep; rw [mp_dd, mp_dk] at this; linarith
  · intro h b; cases b <;> simp only [mp_dk, mp_dd] <;> linarith

end payoffs

lemma fK_eq (s1 p11 p21 : ℝ) (θ : ℝ × ℝ × ℝ) :
    supplierPayoff s1 p11 p21 Action.keep (manufacturerResponse θ Action.keep) =
      -p11 * ({x : ℝ × ℝ × ℝ | x.2.1 < x.1}.indicator 1 θ) := by
  unfold manufacturerResponse
  rw [mp_kk, mp_kd]
  by_cases h : θ.2.1 < θ.1
  · rw [if_pos (by linarith), sp_kd]
    simp [Set.indicator_apply, h]
  · rw [if_neg (by linarith), sp_kk]
    simp [Set.indicator_apply, h]

lemma fD_eq (s1 p11 p21 : ℝ) (θ : ℝ × ℝ × ℝ) :
    supplierPayoff s1 p11 p21 Action.delay (manufacturerResponse θ Action.delay) =
      (s1 - p11) - p21 * ({x : ℝ × ℝ × ℝ | x.2.2 < x.1}.indicator 1 θ) := by
  unfold manufacturerResponse
  rw [mp_dk, mp_dd]
  by_cases h : θ.2.2 < θ.1
  · rw [if_pos (by linarith), sp_dd]
    simp [Set.indicator_apply, h]; ring
  · rw [if_neg (by linarith), sp_dk]
    simp [Set.indicator_apply, h]

lemma measS : MeasurableSet {x : ℝ × ℝ × ℝ | x.2.1 < x.1} :=
  measurableSet_lt (measurable_fst.comp measurable_snd) measurable_fst
lemma measT : MeasurableSet {x : ℝ × ℝ × ℝ | x.2.2 < x.1} :=
  measurableSet_lt (measurable_snd.comp measurable_snd) measurable_fst

lemma muSc (μ : Measure (ℝ × ℝ × ℝ)) (hμ : SupplierBelief μ) :
    μ {x : ℝ × ℝ × ℝ | x.2.1 < x.1}ᶜ = μ lowSavingTypes := by
  obtain ⟨_, hN⟩ := hμ
  apply le_antisymm
  · have hsub : {x : ℝ × ℝ × ℝ | x.2.1 < x.1}ᶜ ⊆
        lowSavingTypes ∪ (lowSavingTypes ∪ mediumSavingTypes ∪ highSavingTypes)ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hx
      by_cases hL : x ∈ lowSavingTypes
      · exact Or.inl hL
      · right
        intro hx'
        rcases hx' with (hx' | hx') | hx'
        · exact hL hx'
        · simp only [mediumSavingTypes, Set.mem_setOf_eq] at hx'; linarith [hx'.1]
        · simp only [highSavingTypes, Set.mem_setOf_eq] at hx'; linarith [hx'.1, hx'.2]
    calc μ {x : ℝ × ℝ × ℝ | x.2.1 < x.1}ᶜ
        ≤ μ (lowSavingTypes ∪ (lowSavingTypes ∪ mediumSavingTypes ∪ highSavingTypes)ᶜ) :=
          measure_mono hsub
      _ ≤ μ lowSavingTypes + μ (lowSavingTypes ∪ mediumSavingTypes ∪ highSavingTypes)ᶜ :=
          measure_union_le _ _
      _ = μ lowSavingTypes := by rw [hN, add_zero]
  · apply measure_mono
    intro x hx
    simp only [lowSavingTypes, Set.mem_setOf_eq] at hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    linarith [hx.1]

lemma muT (μ : Measure (ℝ × ℝ × ℝ)) (hμ : SupplierBelief μ) :
    μ {x : ℝ × ℝ × ℝ | x.2.2 < x.1} = μ highSavingTypes := by
  obtain ⟨_, hN⟩ := hμ
  apply le_antisymm
  · have hsub : {x : ℝ × ℝ × ℝ | x.2.2 < x.1} ⊆
        highSavingTypes ∪ (lowSavingTypes ∪ mediumSavingTypes ∪ highSavingTypes)ᶜ := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      by_cases hH : x ∈ highSavingTypes
      · exact Or.inl hH
      · right
        intro hx'
        rcases hx' with (hx' | hx') | hx'
        · simp only [lowSavingTypes, Set.mem_setOf_eq] at hx'; linarith [hx'.1, hx'.2]
        · simp only [mediumSavingTypes, Set.mem_setOf_eq] at hx'; linarith [hx'.2]
        · exact hH hx'
    calc μ {x : ℝ × ℝ × ℝ | x.2.2 < x.1}
        ≤ μ (highSavingTypes ∪ (lowSavingTypes ∪ mediumSavingTypes ∪ highSavingTypes)ᶜ) :=
          measure_mono hsub
      _ ≤ μ highSavingTypes + μ (lowSavingTypes ∪ mediumSavingTypes ∪ highSavingTypes)ᶜ :=
          measure_union_le _ _
      _ = μ highSavingTypes := by rw [hN, add_zero]
  · apply measure_mono
    intro x hx
    simp only [highSavingTypes, Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq]
    exact hx.2

lemma realS (μ : Measure (ℝ × ℝ × ℝ)) (hμ : SupplierBelief μ) :
    (μ {x : ℝ × ℝ × ℝ | x.2.1 < x.1}).toReal = 1 - qLow μ := by
  have hP : IsProbabilityMeasure μ := hμ.1
  have h1 := measure_add_measure_compl (μ := μ) measS
  rw [measure_univ, muSc μ hμ] at h1
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
  unfold qLow
  simp at h2
  linarith

lemma q_facts (μ : Measure (ℝ × ℝ × ℝ)) (hμ : SupplierBelief μ) :
    0 ≤ qLow μ ∧ 0 ≤ qHigh μ ∧ qLow μ + qHigh μ ≤ 1 := by
  have hP : IsProbabilityMeasure μ := hμ.1
  refine ⟨ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_⟩
  have hsub : highSavingTypes ⊆ {x : ℝ × ℝ × ℝ | x.2.1 < x.1} := by
    intro x hx
    simp only [highSavingTypes, Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq]
    linarith [hx.1, hx.2]
  have := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (μ := μ) hsub)
  rw [realS μ hμ] at this
  unfold qHigh
  linarith

lemma EK_eq (μ : Measure (ℝ × ℝ × ℝ)) (hμ : SupplierBelief μ) (s1 p11 p21 : ℝ) :
    expectedSupplierPayoff μ s1 p11 p21 Action.keep = -p11 * (1 - qLow μ) := by
  unfold expectedSupplierPayoff
  simp_rw [fK_eq]
  rw [integral_const_mul, integral_indicator_one measS, measureReal_def, realS μ hμ]

lemma ED_eq (μ : Measure (ℝ × ℝ × ℝ)) (hμ : SupplierBelief μ) (s1 p11 p21 : ℝ) :
    expectedSupplierPayoff μ s1 p11 p21 Action.delay = (s1 - p11) - p21 * qHigh μ := by
  have hP : IsProbabilityMeasure μ := hμ.1
  unfold expectedSupplierPayoff
  simp_rw [fD_eq]
  have hint : Integrable (fun θ : ℝ × ℝ × ℝ =>
      p21 * ({x : ℝ × ℝ × ℝ | x.2.2 < x.1}.indicator 1 θ)) μ :=
    ((integrable_const (1 : ℝ)).indicator measT).const_mul p21
  rw [integral_sub (integrable_const _) hint, integral_const, integral_const_mul,
    integral_indicator_one measT]
  simp only [measureReal_def]
  rw [muT μ hμ]
  simp [qHigh]

lemma choice_keep (μ : Measure (ℝ × ℝ × ℝ)) (s1 p11 p21 : ℝ) :
    Action.keep ∈ asymmetricSupplierChoices μ s1 p11 p21 ↔
      expectedSupplierPayoff μ s1 p11 p21 Action.delay ≤
        expectedSupplierPayoff μ s1 p11 p21 Action.keep := by
  simp only [asymmetricSupplierChoices, Set.mem_setOf_eq]
  constructor
  · intro h; exact h _
  · intro h b; cases b
    · exact le_refl _
    · exact h

lemma choice_delay (μ : Measure (ℝ × ℝ × ℝ)) (s1 p11 p21 : ℝ) :
    Action.delay ∈ asymmetricSupplierChoices μ s1 p11 p21 ↔
      expectedSupplierPayoff μ s1 p11 p21 Action.keep ≤
        expectedSupplierPayoff μ s1 p11 p21 Action.delay := by
  simp only [asymmetricSupplierChoices, Set.mem_setOf_eq]
  constructor
  · intro h; exact h _
  · intro h b; cases b
    · exact h
    · exact le_refl _

/-- canonical manufacturer strategy: delay iff strictly better. -/
noncomputable def sig0 (s0 p10 p20 : ℝ) : Action → Action
  | Action.keep => if p10 < s0 then Action.delay else Action.keep
  | Action.delay => if p20 < s0 then Action.delay else Action.keep

lemma sig0_br (s0 p10 p20 : ℝ) (a : Action) :
    sig0 s0 p10 p20 a ∈ manufacturerBestResponses s0 p10 p20 a := by
  cases a
  · simp only [sig0]
    split_ifs with h
    · exact (br_kd _ _ _).2 h.le
    · exact (br_kk _ _ _).2 (not_lt.1 h)
  · simp only [sig0]
    split_ifs with h
    · exact (br_dd _ _ _).2 h.le
    · exact (br_dk _ _ _).2 (not_lt.1 h)

/-- a symmetric SPNE outcome exists, built from any best-responding strategy. -/
lemma sym_exists (s1 p11 p21 s0 p10 p20 : ℝ) (σ : Action → Action)
    (hσ : ∀ a, σ a ∈ manufacturerBestResponses s0 p10 p20 a) :
    ∃ b, (b, σ b) ∈ symmetricSPNEOutcomes s1 p11 p21 s0 p10 p20 := by
  by_cases h : supplierPayoff s1 p11 p21 Action.delay (σ Action.delay) ≤
      supplierPayoff s1 p11 p21 Action.keep (σ Action.keep)
  · refine ⟨Action.keep, σ, hσ, ?_, rfl⟩
    intro b; cases b
    · exact le_refl _
    · exact h
  · refine ⟨Action.delay, σ, hσ, ?_, rfl⟩
    intro b; cases b
    · exact (not_le.1 h).le
    · exact le_refl _

lemma pd_le_two (a b : Action) : projectDelay a b ≤ 2 := by
  cases a <;> cases b <;> decide

lemma main (s1 s0 p11 p21 p10 p20 : ℝ)
    (μ : Measure (ℝ × ℝ × ℝ)) (hμ : SupplierBelief μ)
    (hC2 : Condition2 s1 s0 p11 p21 p10 p20) (hsign : 0 < s1 ∨ 0 ≤ p21) :
    AsymmetryShortensDuration μ s1 p11 p21 s0 p10 p20 ↔
      (p11 < s1 ∧ s1 < p21) ∧ (s0 < p10 ∧ p10 < p20) ∧
        s1 < p11 * qLow μ + p21 * qHigh μ := by
  obtain ⟨hql, hqh, hq1⟩ := q_facts μ hμ
  have hEK := EK_eq μ hμ s1 p11 p21
  have hED := ED_eq μ hμ s1 p11 p21
  obtain ⟨⟨_, _⟩, ⟨_, h1121, h1020⟩⟩ := hC2
  -- s1 < thr implies s1 < p21
  have hthr : ∀ _ : s1 < p11 * qLow μ + p21 * qHigh μ, s1 < p21 := by
    intro hs
    have hA : p11 * qLow μ ≤ p21 * qLow μ := mul_le_mul_of_nonneg_right h1121.le hql
    rcases le_or_gt 0 p21 with hp | hp
    · have : p21 * (qLow μ + qHigh μ) ≤ p21 := mul_le_of_le_one_right hp hq1
      nlinarith
    · rcases hsign with hs1 | hs1
      · have : p21 * (qLow μ + qHigh μ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hp.le (add_nonneg hql hqh)
        nlinarith
      · linarith
  unfold AsymmetryShortensDuration
  constructor
  · intro H
    -- F3: s1 < thr
    have F3 : s1 < p11 * qLow μ + p21 * qHigh μ := by
      by_contra hcon
      push_neg at hcon
      have hD : Action.delay ∈ asymmetricSupplierChoices μ s1 p11 p21 := by
        rw [choice_delay, hEK, hED]; linarith
      obtain ⟨b, hb⟩ := sym_exists s1 p11 p21 s0 p10 p20 (sig0 s0 p10 p20) (sig0_br s0 p10 p20)
      have hbr := sig0_br s0 p10 p20 Action.delay
      have hlt := H (Action.delay, sig0 s0 p10 p20 Action.delay) ⟨hD, hbr⟩ _ hb
      simp only at hlt
      by_cases h20 : p20 < s0
      · have e : sig0 s0 p10 p20 Action.delay = Action.delay := by simp [sig0, h20]
        rw [e, pd_dd] at hlt
        have h2 := pd_le_two b (sig0 s0 p10 p20 b)
        exact absurd (lt_of_lt_of_le hlt h2) (lt_irrefl 2)
      · have e : sig0 s0 p10 p20 Action.delay = Action.keep := by simp [sig0, h20]
        rw [e, pd_dk] at hlt
        cases b
        · have h2 : projectDelay Action.keep (sig0 s0 p10 p20 Action.keep) ≤ 1 := by
            simp only [sig0]; split_ifs <;> decide
          exact absurd (lt_of_lt_of_le hlt h2) (lt_irrefl 1)
        · rw [e, pd_dk] at hlt
          exact absurd hlt (lt_irrefl 1)
    have hs21 := hthr F3
    have hK : Action.keep ∈ asymmetricSupplierChoices μ s1 p11 p21 := by
      rw [choice_keep, hEK, hED]; linarith
    -- F1: s0 < p10
    have F1 : s0 < p10 := by
      by_contra hcon
      push_neg at hcon
      have hbrK : Action.delay ∈ manufacturerBestResponses s0 p10 p20 Action.keep :=
        (br_kd _ _ _).2 hcon
      by_cases h20 : p20 < s0
      · have hsK : sig0 s0 p10 p20 Action.keep = Action.delay := by
          simp [sig0]; linarith
        have hsD : sig0 s0 p10 p20 Action.delay = Action.delay := by simp [sig0, h20]
        have hkeep : (Action.keep, sig0 s0 p10 p20 Action.keep) ∈
            symmetricSPNEOutcomes s1 p11 p21 s0 p10 p20 := by
          refine ⟨sig0 s0 p10 p20, sig0_br s0 p10 p20, ?_, rfl⟩
          intro b; cases b
          · exact le_refl _
          · rw [hsK, hsD, sp_dd, sp_kd]; linarith
        have := H (Action.keep, Action.delay) ⟨hK, hbrK⟩ _ hkeep
        simp only at this
        rw [hsK, pd_kd] at this
        omega
      · have hsD : sig0 s0 p10 p20 Action.delay = Action.keep := by simp [sig0, h20]
        obtain ⟨b, hb⟩ :=
          sym_exists s1 p11 p21 s0 p10 p20 (sig0 s0 p10 p20) (sig0_br s0 p10 p20)
        have := H (Action.keep, Action.delay) ⟨hK, hbrK⟩ _ hb
        simp only at this
        rw [pd_kd] at this
        cases b
        · have : projectDelay Action.keep (sig0 s0 p10 p20 Action.keep) ≤ 1 := by
            simp only [sig0]; split_ifs <;> decide
          omega
        · rw [hsD, pd_dk] at this
          omega
    -- F2: p11 < s1
    have F2 : p11 < s1 := by
      by_contra hcon
      push_neg at hcon
      have hbrK : Action.keep ∈ manufacturerBestResponses s0 p10 p20 Action.keep :=
        (br_kk _ _ _).2 F1.le
      have hsK : sig0 s0 p10 p20 Action.keep = Action.keep := by
        simp [sig0]; linarith
      have hsD : sig0 s0 p10 p20 Action.delay = Action.keep := by
        simp [sig0]; linarith
      have hkeep : (Action.keep, sig0 s0 p10 p20 Action.keep) ∈
          symmetricSPNEOutcomes s1 p11 p21 s0 p10 p20 := by
        refine ⟨sig0 s0 p10 p20, sig0_br s0 p10 p20, ?_, rfl⟩
        intro b; cases b
        · exact le_refl _
        · rw [hsK, hsD, sp_dk, sp_kk]; linarith
      have := H (Action.keep, Action.keep) ⟨hK, hbrK⟩ _ hkeep
      simp only at this
      rw [hsK, pd_kk] at this
      omega
    exact ⟨⟨F2, hs21⟩, ⟨F1, h1020⟩, F3⟩
  · rintro ⟨⟨h11, h21⟩, ⟨h10, h20⟩, hthr'⟩
    rintro ⟨a1, a0⟩ ⟨ha1, ha0⟩ ⟨b1, b0⟩ ⟨σ, hσ, hopt, hb0⟩
    simp only at ha1 ha0 hopt hb0 ⊢
    -- asymmetric: a1 = keep, a0 = keep
    have ea1 : a1 = Action.keep := by
      cases a1
      · rfl
      · rw [choice_delay, hEK, hED] at ha1; exfalso; linarith
    subst ea1
    have ea0 : a0 = Action.keep := by
      cases a0
      · rfl
      · rw [br_kd] at ha0; exfalso; linarith
    subst ea0
    -- symmetric: σ delay = keep, then b1 = delay
    have hσD : σ Action.delay = Action.keep := by
      have := hσ Action.delay
      revert this
      cases σ Action.delay
      · intro _; rfl
      · intro h; rw [br_dd] at h; exfalso; linarith
    have hσK : σ Action.keep = Action.keep := by
      have := hσ Action.keep
      revert this
      cases σ Action.keep
      · intro _; rfl
      · intro h; rw [br_kd] at h; exfalso; linarith
    have eb1 : b1 = Action.delay := by
      cases b1
      · have := hopt Action.delay
        rw [hσD, hσK, sp_dk, sp_kk] at this
        exfalso; linarith
      · rfl
    subst eb1
    rw [hb0, hσD, pd_kk, pd_dk]
    decide

end RSPT6

open RiskSharingProjects.TimeDependent in
theorem solution (s1 s0 p11 p21 p10 p20 : ℝ)
    (μ : MeasureTheory.Measure (ℝ × ℝ × ℝ)) (hμ : SupplierBelief μ)
    (hC2 : Condition2 s1 s0 p11 p21 p10 p20) (hsign : 0 < s1 ∨ 0 ≤ p21) :
    AsymmetryShortensDuration μ s1 p11 p21 s0 p10 p20 ↔
      (p11 < s1 ∧ s1 < p21) ∧ (s0 < p10 ∧ p10 < p20) ∧
        s1 < p11 * qLow μ + p21 * qHigh μ := by
  exact RSPT6.main s1 s0 p11 p21 p10 p20 μ hμ hC2 hsign
