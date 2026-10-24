-- Prove2me | solution 1 for SampleComplexityRL.MuPolicySearch.mu_optimality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T16:20:53.798147+00:00
-- url     : https://prove2.me/submissions/d482e151-7e0e-41a5-8838-b4c89efee4f7

import Mathlib
import Definitions.Def_SampleComplexityRL_MuPolicySearch_MuReset

set_option autoImplicit false

namespace MuOptAuxee0970a3

open FoundationsML.ReinforcementLearning

theorem wavg {A : Type} [Fintype A] (w f : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (lo hi : ℝ) (hf : ∀ a, lo ≤ f a ∧ f a ≤ hi) :
    lo ≤ ∑ a, w a * f a ∧ ∑ a, w a * f a ≤ hi := by
  constructor
  · calc lo = ∑ a, w a * lo := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ ∑ a, w a * f a :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hf a).1 (hw a))
  · calc ∑ a, w a * f a ≤ ∑ a, w a * hi :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hf a).2 (hw a))
      _ = hi := by rw [← Finset.sum_mul, hs, one_mul]

theorem tele (D g : ℕ → ℝ) (T : ℕ) (hD : ∀ t < T, D t = g t + D (t + 1)) :
    ∀ n ≤ T, D 0 = ∑ t ∈ Finset.range n, g t + D n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [ih (by omega), hD n (by omega), Finset.sum_range_succ]
    ring

/-- value bounds: `0 ≤ V_{π,t}(s) ≤ (T - t)/T` for `t ≤ T`. -/
theorem vbound {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (hT : 0 < T)
    (π : SampleComplexityRL.PolicyGrad.NSPolicy S A) (hπ : SampleComplexityRL.PolicyGrad.IsNSPolicy T π) :
    ∀ k t, t + k = T → ∀ s, 0 ≤ SampleComplexityRL.PolicyGrad.tValue P r T π t s ∧
      SampleComplexityRL.PolicyGrad.tValue P r T π t s ≤ ((T : ℝ) - t) / T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  intro k
  induction k with
  | zero =>
    intro t ht s
    rw [SampleComplexityRL.PolicyGrad.tValue.eq_1, if_neg (by omega)]
    have : (t : ℝ) = T := by exact_mod_cast (by omega : t = T)
    rw [this]; simp
  | succ k ih =>
    intro t ht s
    rw [SampleComplexityRL.PolicyGrad.tValue.eq_1, if_pos (by omega)]
    obtain ⟨hnn, hsum⟩ := hπ t (by omega) s
    apply wavg _ _ hnn hsum
    intro a
    obtain ⟨hpn, hps⟩ := hP s a
    have hW := wavg (P s a) (fun s' => SampleComplexityRL.PolicyGrad.tValue P r T π (t + 1) s')
      hpn hps 0 (((T : ℝ) - (t + 1 : ℕ)) / T) (fun s' => ih (t + 1) (by omega) s')
    obtain ⟨hr0, hr1⟩ := hr s a
    have h1 : (1 / (T : ℝ)) * r s a ≤ 1 / T := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hr1 hTpos.le
    have h0 : 0 ≤ (1 / (T : ℝ)) * r s a := mul_nonneg (by positivity) hr0
    have he : (1 / (T : ℝ)) + ((T : ℝ) - (t + 1 : ℕ)) / T = ((T : ℝ) - t) / T := by
      push_cast; field_simp; ring
    constructor <;> linarith [hW.1, hW.2]

end MuOptAuxee0970a3

open SampleComplexityRL.MuPolicySearch FoundationsML.ReinforcementLearning in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ)
    (hP : IsTransitionKernel P) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (hT : 0 < T)
    (μ : ℕ → S → ℝ) (hμ : IsResetDist T μ) (Pi1 : Set (S → A)) (ε : ℝ)
    (π : SampleComplexityRL.PolicyGrad.NSPolicy S A) (hπ : SampleComplexityRL.PolicyGrad.IsNSPolicy T π)
    (hadv : ∀ h ∈ Pi1, ∀ t < T, muAdvantage P r T π μ t h ≤ ε / T) :
    ∀ π' : ℕ → S → A, InPolicyClass Pi1 T π' → ∀ s₀ : S,
      SampleComplexityRL.PolicyGrad.value P r T (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ - ε -
          (T : ℝ) * stateTimeL1 T (SampleComplexityRL.Mismeasure.stateTimeDist P (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ T) (resetJoint T μ) ≤
        SampleComplexityRL.PolicyGrad.value P r T π s₀ := by
  intro π' hπ' s₀
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hTne : (T : ℝ) ≠ 0 := hTpos.ne'
  set V' := SampleComplexityRL.PolicyGrad.tValue P r T (SampleComplexityRL.Mismeasure.detNSPolicy π')
    with hV'
  set V := SampleComplexityRL.PolicyGrad.tValue P r T π with hV
  set d := SampleComplexityRL.Mismeasure.stateDist P (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀
    with hd
  set Adv := fun t s => SampleComplexityRL.PolicyGrad.tAdvantage P r T π t s (π' t s) with hAdv
  -- one-step identity
  have hstep : ∀ t < T, ∀ s, V' t s - V t s =
      Adv t s + ∑ s', P s (π' t s) s' * (V' (t + 1) s' - V (t + 1) s') := by
    intro t ht s
    have hdet : V' t s = SampleComplexityRL.PolicyGrad.tQValue P r T
        (SampleComplexityRL.Mismeasure.detNSPolicy π') t s (π' t s) := by
      rw [hV', SampleComplexityRL.PolicyGrad.tValue.eq_1, if_pos ht]
      simp only [SampleComplexityRL.Mismeasure.detNSPolicy, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    rw [hdet]
    simp only [hAdv, SampleComplexityRL.PolicyGrad.tAdvantage, SampleComplexityRL.PolicyGrad.tQValue,
      mul_sub, Finset.sum_sub_distrib, hV', hV]
    ring
  -- propagation of the state distribution
  have hprop : ∀ t, ∀ X : S → ℝ,
      ∑ s, d t s * ∑ s', P s (π' t s) s' * X s' = ∑ s', d (t + 1) s' * X s' := by
    intro t X
    have hdt : ∀ s', d (t + 1) s' = ∑ s, d t s * P s (π' t s) s' := by
      intro s'
      rw [hd]
      simp only [SampleComplexityRL.Mismeasure.stateDist, SampleComplexityRL.Mismeasure.detNSPolicy,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [hdt, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun s' _ => ?_))
    ring
  set D := fun t => ∑ s, d t s * (V' t s - V t s) with hD
  have hDrec : ∀ t < T, D t = (∑ s, d t s * Adv t s) + D (t + 1) := by
    intro t ht
    simp only [hD]
    rw [← hprop t (fun s' => V' (t + 1) s' - V (t + 1) s'), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hstep t ht s]; ring
  have hDT : D T = 0 := by
    simp only [hD]
    refine Finset.sum_eq_zero (fun s _ => ?_)
    rw [hV', hV, SampleComplexityRL.PolicyGrad.tValue.eq_1 P r T _ T s,
      SampleComplexityRL.PolicyGrad.tValue.eq_1 P r T π T s, if_neg (lt_irrefl T),
      if_neg (lt_irrefl T)]
    ring
  have hD0 : D 0 = V' 0 s₀ - V 0 s₀ := by
    simp only [hD, hd, SampleComplexityRL.Mismeasure.stateDist, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have htel := MuOptAuxee0970a3.tele D (fun t => ∑ s, d t s * Adv t s) T hDrec T le_rfl
  rw [hDT, add_zero, hD0] at htel
  -- advantage bound
  have hAb : ∀ t < T, ∀ s, |Adv t s| ≤ 1 := by
    intro t ht s
    have hb := MuOptAuxee0970a3.vbound P r T hP hr hT π hπ
    have h1 := hb (T - t) t (by omega) s
    have hW := MuOptAuxee0970a3.wavg (P s (π' t s)) (fun s' => V (t + 1) s')
      (hP s (π' t s)).1 (hP s (π' t s)).2 0 (((T : ℝ) - (t + 1 : ℕ)) / T)
      (fun s' => hb (T - (t + 1)) (t + 1) (by omega) s')
    obtain ⟨hr0, hr1⟩ := hr s (π' t s)
    have hq1 : (1 / (T : ℝ)) * r s (π' t s) ≤ 1 / T := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hr1 hTpos.le
    have hq0 : 0 ≤ (1 / (T : ℝ)) * r s (π' t s) := mul_nonneg (by positivity) hr0
    have he : (1 / (T : ℝ)) + ((T : ℝ) - (t + 1 : ℕ)) / T = ((T : ℝ) - t) / T := by
      push_cast; field_simp; ring
    have hle : ((T : ℝ) - t) / T ≤ 1 := by
      rw [div_le_one hTpos]; have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith
    have hAeq : Adv t s = (1 / (T : ℝ)) * r s (π' t s) + ∑ s', P s (π' t s) s' * V (t + 1) s'
        - V t s := by
      simp only [hAdv, SampleComplexityRL.PolicyGrad.tAdvantage, SampleComplexityRL.PolicyGrad.tQValue,
        hV]
    rw [hAeq, abs_le]
    constructor <;> linarith [hW.1, hW.2, h1.1, h1.2]
  -- per-time bound
  have hper : ∀ t ∈ Finset.range T, ∑ s, d t s * Adv t s ≤
      ε / T + (T : ℝ) * ∑ s, |SampleComplexityRL.Mismeasure.stateTimeDist P
        (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ T s t - resetJoint T μ s t| := by
    intro t htm
    have ht : t < T := Finset.mem_range.mp htm
    have hsplit : ∀ s, d t s * Adv t s = μ t s * Adv t s + (T : ℝ) *
        ((SampleComplexityRL.Mismeasure.stateTimeDist P
          (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ T s t - resetJoint T μ s t) * Adv t s) := by
      intro s
      simp only [SampleComplexityRL.Mismeasure.stateTimeDist, resetJoint, if_pos ht, hd]
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ s, μ t s * Adv t s ≤ ε / T := hadv (π' t) (hπ' t ht) t ht
    have h2 : ∑ s, (SampleComplexityRL.Mismeasure.stateTimeDist P
          (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ T s t - resetJoint T μ s t) * Adv t s
        ≤ ∑ s, |SampleComplexityRL.Mismeasure.stateTimeDist P
          (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ T s t - resetJoint T μ s t| := by
      refine Finset.sum_le_sum (fun s _ => ?_)
      calc _ ≤ |(SampleComplexityRL.Mismeasure.stateTimeDist P
            (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ T s t - resetJoint T μ s t) * Adv t s| :=
            le_abs_self _
        _ = _ * |Adv t s| := abs_mul _ _
        _ ≤ _ * 1 := mul_le_mul_of_nonneg_left (hAb t ht s) (abs_nonneg _)
        _ = _ := mul_one _
    have := mul_le_mul_of_nonneg_left h2 hTpos.le
    linarith
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hL1 : ∑ t ∈ Finset.range T, ∑ s, |SampleComplexityRL.Mismeasure.stateTimeDist P
        (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ T s t - resetJoint T μ s t|
      = stateTimeL1 T (SampleComplexityRL.Mismeasure.stateTimeDist P
          (SampleComplexityRL.Mismeasure.detNSPolicy π') s₀ T) (resetJoint T μ) := by
    unfold stateTimeL1
    exact Finset.sum_comm
  rw [hL1, mul_div_cancel₀ ε hTne] at hsum
  show V' 0 s₀ - ε - _ ≤ V 0 s₀
  linarith
