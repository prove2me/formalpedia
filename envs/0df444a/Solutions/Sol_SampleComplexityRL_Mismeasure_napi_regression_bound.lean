-- Prove2me | solution 1 for SampleComplexityRL.Mismeasure.napi_regression_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T02:43:57.39001+00:00
-- url     : https://prove2.me/submissions/73bb77c5-fe68-4452-a4e0-033cffb1045b

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_SampleComplexityRL_Mismeasure_TEpoch
import Definitions.Def_SampleComplexityRL_Mismeasure_NAPI

set_option autoImplicit false

namespace NapiAux05185744

open SampleComplexityRL SampleComplexityRL.Mismeasure FoundationsML.ReinforcementLearning

theorem tValue_congr {S A : Type} [Fintype S] [Fintype A] (P : S → A → S → ℝ) (r : S → A → ℝ)
    (T : ℕ) (π₁ π₂ : PolicyGrad.NSPolicy S A) :
    ∀ n k, T - k = n → (∀ τ, k ≤ τ → π₁ τ = π₂ τ) →
      PolicyGrad.tValue P r T π₁ k = PolicyGrad.tValue P r T π₂ k := by
  intro n
  induction n with
  | zero =>
    intro k hk _
    funext s
    rw [PolicyGrad.tValue.eq_1 P r T π₁ k s, PolicyGrad.tValue.eq_1 P r T π₂ k s]
    have : ¬ k < T := by omega
    simp [this]
  | succ n ih =>
    intro k hk hagree
    funext s
    have hkT : k < T := by omega
    have hn := ih (k + 1) (by omega) (fun τ hτ => hagree τ (by omega))
    rw [PolicyGrad.tValue.eq_1 P r T π₁ k s, PolicyGrad.tValue.eq_1 P r T π₂ k s, if_pos hkT,
      if_pos hkT, hn, hagree k le_rfl]

theorem napi_apply {S A : Type} (T : ℕ) (init h : ℕ → S → A) :
    ∀ n j, T - j = n → ∀ τ,
      napiPolicy T init h j τ = if j ≤ τ ∧ τ < T then h τ else init τ := by
  intro n
  induction n with
  | zero =>
    intro j hj τ
    rw [napiPolicy, if_neg (by omega), if_neg (by omega)]
  | succ n ih =>
    intro j hj τ
    rw [napiPolicy, if_pos (by omega)]
    simp only [setRule]
    by_cases h1 : τ = j
    · rw [if_pos h1, if_pos (by omega), h1]
    · rw [if_neg h1, ih (j + 1) (by omega) τ]
      by_cases h2 : j + 1 ≤ τ ∧ τ < T
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem q_gap_le {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : ℕ → S → A) (t : ℕ) (Q : S → A → ℝ)
    (hs : S → A) (hg : ∀ s a, Q s a ≤ Q s (hs s)) (s : S) (a : A) :
    PolicyGrad.tQValue P r T (detNSPolicy π) t s a
        - PolicyGrad.tQValue P r T (detNSPolicy π) t s (hs s)
      ≤ 2 * regressionError P r T π t Q s := by
  have h1 : |PolicyGrad.tQValue P r T (detNSPolicy π) t s a - Q s a|
      ≤ regressionError P r T π t Q s := by
    unfold regressionError
    exact Finset.le_sup' (fun a => |PolicyGrad.tQValue P r T (detNSPolicy π) t s a - Q s a|)
      (Finset.mem_univ a)
  have h2 : |PolicyGrad.tQValue P r T (detNSPolicy π) t s (hs s) - Q s (hs s)|
      ≤ regressionError P r T π t Q s := by
    unfold regressionError
    exact Finset.le_sup' (fun a => |PolicyGrad.tQValue P r T (detNSPolicy π) t s a - Q s a|)
      (Finset.mem_univ (hs s))
  have h3 := hg s a
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

theorem tele (D g : ℕ → ℝ) (T : ℕ) (h0 : ∀ k, T ≤ k → D k = 0)
    (hstep : ∀ k, k < T → D k ≤ g k + D (k + 1)) :
    D 0 ≤ ∑ t ∈ Finset.range T, g t := by
  have key : ∀ n k, T - k = n → D k ≤ ∑ t ∈ Finset.Ico k T, g t := by
    intro n
    induction n with
    | zero =>
      intro k hk
      rw [h0 k (by omega), Finset.Ico_eq_empty_of_le (by omega : T ≤ k)]
      simp
    | succ n ih =>
      intro k hk
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : k < T)]
      linarith [hstep k (by omega), ih (k + 1) (by omega)]
  rw [Finset.range_eq_Ico]
  exact key T 0 (by omega)

theorem swap_sum {S A : Type} [Fintype S] [Fintype A] (μ : S → ℝ) (π : S → A → ℝ)
    (P : S → A → S → ℝ) (d : S → ℝ) :
    ∑ s, μ s * ∑ a, π s a * ∑ s', P s a s' * d s'
      = ∑ s', (∑ s, μ s * ∑ a, π s a * P s a s') * d s' := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  ring

end NapiAux05185744

open SampleComplexityRL.Mismeasure FoundationsML.ReinforcementLearning in
theorem solution {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (T : ℕ) (hT : 0 < T)
    (init : ℕ → S → A) (Qtil : ℕ → S → A → ℝ) (h : ℕ → S → A)
    (hgreedy : ∀ t, t < T → ∀ s a, Qtil t s a ≤ Qtil t s (h t s))
    (π' : SampleComplexityRL.PolicyGrad.NSPolicy S A) (hπ' : SampleComplexityRL.PolicyGrad.IsNSPolicy T π') (s₀ : S) :
    SampleComplexityRL.PolicyGrad.value P r T (detNSPolicy (napiPolicy T init h 0)) s₀ ≥
      SampleComplexityRL.PolicyGrad.value P r T π' s₀ - 2 * (T : ℝ) * ∑ t ∈ Finset.range T, ∑ s,
        stateTimeDist P π' s₀ T s t *
          regressionError P r T (napiPolicy T init h (t + 1)) t (Qtil t) s := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  -- the returned policy agrees with the input policy of update t from time t+1 on
  have hagree : ∀ t τ, t + 1 ≤ τ → detNSPolicy (napiPolicy T init h 0) τ
      = detNSPolicy (napiPolicy T init h (t + 1)) τ := by
    intro t τ hτ
    funext s a
    simp only [detNSPolicy]
    rw [NapiAux05185744.napi_apply T init h (T - 0) 0 rfl τ,
      NapiAux05185744.napi_apply T init h (T - (t + 1)) (t + 1) rfl τ]
    by_cases hτT : τ < T
    · simp [hτT, hτ]
    · simp [hτT]
  have hQeq : ∀ t s a,
      SampleComplexityRL.PolicyGrad.tQValue P r T (detNSPolicy (napiPolicy T init h 0)) t s a
        = SampleComplexityRL.PolicyGrad.tQValue P r T
            (detNSPolicy (napiPolicy T init h (t + 1))) t s a := by
    intro t s a
    have hV := NapiAux05185744.tValue_congr P r T (detNSPolicy (napiPolicy T init h 0))
      (detNSPolicy (napiPolicy T init h (t + 1))) _ (t + 1) rfl (hagree t)
    simp only [SampleComplexityRL.PolicyGrad.tQValue, hV]
  have hVd : ∀ t, t < T → ∀ s,
      SampleComplexityRL.PolicyGrad.tValue P r T (detNSPolicy (napiPolicy T init h 0)) t s
        = SampleComplexityRL.PolicyGrad.tQValue P r T (detNSPolicy (napiPolicy T init h 0))
            t s (h t s) := by
    intro t ht s
    have hn : napiPolicy T init h 0 t s = h t s := by
      rw [NapiAux05185744.napi_apply T init h (T - 0) 0 rfl t, if_pos ⟨Nat.zero_le t, ht⟩]
    rw [SampleComplexityRL.PolicyGrad.tValue.eq_1, if_pos ht]
    simp only [detNSPolicy, hn, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl
  have hμnn : ∀ t, t ≤ T → ∀ s, 0 ≤ stateDist P π' s₀ t s := by
    intro t
    induction t with
    | zero => intro _ s; simp only [stateDist]; split_ifs <;> norm_num
    | succ t ih =>
      intro ht s'
      simp only [stateDist]
      refine Finset.sum_nonneg (fun s _ => mul_nonneg (ih (by omega) s) ?_)
      refine Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ' t (by omega) s).1 a) ?_)
      exact (hP s a).1 s'
  -- pointwise one-step bound
  have hpt : ∀ t, t < T → ∀ s,
      SampleComplexityRL.PolicyGrad.tValue P r T π' t s
        - SampleComplexityRL.PolicyGrad.tValue P r T (detNSPolicy (napiPolicy T init h 0)) t s
      ≤ ∑ a, π' t s a * ∑ s', P s a s' *
          (SampleComplexityRL.PolicyGrad.tValue P r T π' (t + 1) s'
            - SampleComplexityRL.PolicyGrad.tValue P r T
                (detNSPolicy (napiPolicy T init h 0)) (t + 1) s')
        + 2 * regressionError P r T (napiPolicy T init h (t + 1)) t (Qtil t) s := by
    intro t ht s
    obtain ⟨hnn, hsum⟩ := hπ' t ht s
    have hgap : ∀ a,
        SampleComplexityRL.PolicyGrad.tQValue P r T (detNSPolicy (napiPolicy T init h 0)) t s a
          - SampleComplexityRL.PolicyGrad.tQValue P r T (detNSPolicy (napiPolicy T init h 0))
              t s (h t s)
        ≤ 2 * regressionError P r T (napiPolicy T init h (t + 1)) t (Qtil t) s := by
      intro a
      rw [hQeq, hQeq]
      exact NapiAux05185744.q_gap_le P r T _ t (Qtil t) (h t) (hgreedy t ht) s a
    rw [SampleComplexityRL.PolicyGrad.tValue.eq_1 P r T π' t s, if_pos ht, hVd t ht s]
    have key : ∀ a, π' t s a * ((1 / (T : ℝ)) * r s a
        + ∑ s', P s a s' * SampleComplexityRL.PolicyGrad.tValue P r T π' (t + 1) s')
        = π' t s a * ∑ s', P s a s' *
            (SampleComplexityRL.PolicyGrad.tValue P r T π' (t + 1) s'
              - SampleComplexityRL.PolicyGrad.tValue P r T
                  (detNSPolicy (napiPolicy T init h 0)) (t + 1) s')
          + π' t s a * (SampleComplexityRL.PolicyGrad.tQValue P r T
                (detNSPolicy (napiPolicy T init h 0)) t s a
              - SampleComplexityRL.PolicyGrad.tQValue P r T
                (detNSPolicy (napiPolicy T init h 0)) t s (h t s))
          + π' t s a * SampleComplexityRL.PolicyGrad.tQValue P r T
                (detNSPolicy (napiPolicy T init h 0)) t s (h t s) := by
      intro a
      simp only [SampleComplexityRL.PolicyGrad.tQValue, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, hsum, one_mul]
    have hb : ∑ a, π' t s a * (SampleComplexityRL.PolicyGrad.tQValue P r T
                (detNSPolicy (napiPolicy T init h 0)) t s a
              - SampleComplexityRL.PolicyGrad.tQValue P r T
                (detNSPolicy (napiPolicy T init h 0)) t s (h t s))
        ≤ ∑ a, π' t s a * (2 * regressionError P r T (napiPolicy T init h (t + 1)) t (Qtil t) s) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hgap a) (hnn a))
    rw [← Finset.sum_mul, hsum, one_mul] at hb
    linarith
  -- telescoping over time
  have htel := NapiAux05185744.tele
    (fun k => ∑ s, stateDist P π' s₀ k s *
      (SampleComplexityRL.PolicyGrad.tValue P r T π' k s
        - SampleComplexityRL.PolicyGrad.tValue P r T (detNSPolicy (napiPolicy T init h 0)) k s))
    (fun t => 2 * ∑ s, stateDist P π' s₀ t s *
      regressionError P r T (napiPolicy T init h (t + 1)) t (Qtil t) s) T
    (by
      intro k hk
      refine Finset.sum_eq_zero (fun s _ => ?_)
      rw [SampleComplexityRL.PolicyGrad.tValue.eq_1 P r T π' k s,
        SampleComplexityRL.PolicyGrad.tValue.eq_1 P r T _ k s, if_neg (by omega),
        if_neg (by omega)]
      ring)
    (by
      intro k hk
      have h1 : ∑ s, stateDist P π' s₀ k s *
          (SampleComplexityRL.PolicyGrad.tValue P r T π' k s
            - SampleComplexityRL.PolicyGrad.tValue P r T (detNSPolicy (napiPolicy T init h 0)) k s)
          ≤ ∑ s, stateDist P π' s₀ k s *
            (∑ a, π' k s a * ∑ s', P s a s' *
              (SampleComplexityRL.PolicyGrad.tValue P r T π' (k + 1) s'
                - SampleComplexityRL.PolicyGrad.tValue P r T
                    (detNSPolicy (napiPolicy T init h 0)) (k + 1) s')
            + 2 * regressionError P r T (napiPolicy T init h (k + 1)) k (Qtil k) s) :=
        Finset.sum_le_sum (fun s _ =>
          mul_le_mul_of_nonneg_left (hpt k hk s) (hμnn k (by omega) s))
      have h2 := NapiAux05185744.swap_sum (stateDist P π' s₀ k) (π' k) P
        (fun s' => SampleComplexityRL.PolicyGrad.tValue P r T π' (k + 1) s'
          - SampleComplexityRL.PolicyGrad.tValue P r T
              (detNSPolicy (napiPolicy T init h 0)) (k + 1) s')
      have h3 : ∀ s', stateDist P π' s₀ (k + 1) s'
          = ∑ s, stateDist P π' s₀ k s * ∑ a, π' k s a * P s a s' := fun s' => rfl
      simp only [mul_add, Finset.sum_add_distrib] at h1
      simp only [← h3] at h2
      rw [h2] at h1
      have h4 : ∑ s, stateDist P π' s₀ k s *
            (2 * regressionError P r T (napiPolicy T init h (k + 1)) k (Qtil k) s)
          = 2 * ∑ s, stateDist P π' s₀ k s *
            regressionError P r T (napiPolicy T init h (k + 1)) k (Qtil k) s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        ring
      linarith)
  have hD0 : ∑ s, stateDist P π' s₀ 0 s *
      (SampleComplexityRL.PolicyGrad.tValue P r T π' 0 s
        - SampleComplexityRL.PolicyGrad.tValue P r T (detNSPolicy (napiPolicy T init h 0)) 0 s)
      = SampleComplexityRL.PolicyGrad.value P r T π' s₀
        - SampleComplexityRL.PolicyGrad.value P r T (detNSPolicy (napiPolicy T init h 0)) s₀ := by
    simp only [stateDist, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, SampleComplexityRL.PolicyGrad.value]
  have hR : 2 * (T : ℝ) * ∑ t ∈ Finset.range T, ∑ s,
        stateTimeDist P π' s₀ T s t *
          regressionError P r T (napiPolicy T init h (t + 1)) t (Qtil t) s
      = ∑ t ∈ Finset.range T, 2 * ∑ s, stateDist P π' s₀ t s *
          regressionError P r T (napiPolicy T init h (t + 1)) t (Qtil t) s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have htT : t < T := Finset.mem_range.mp ht
    simp only [stateTimeDist, if_pos htT, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    field_simp
  rw [hD0] at htel
  rw [ge_iff_le, hR]
  linarith
