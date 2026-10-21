-- Prove2me | solution 1 for SampleComplexityRL.Exploration.eps_approx_condition
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:45:18.430412+00:00
-- url     : https://prove2.me/submissions/3ee601fc-cc83-4c04-9faa-5ac73ffad79f

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_SampleComplexityRL_Exploration_Model

set_option autoImplicit false
open SampleComplexityRL.Exploration FoundationsML.ReinforcementLearning

namespace SCRAux

theorem esc_eq {S A : Type} [Fintype S] [DecidableEq S]
    (P : S → A → S → ℝ) (K : Finset S) (T : ℕ) (π : ℕ → S → A) (t : ℕ) (s : S) :
    escapeProb P K T π t s =
      if t < T then
        (if s ∈ K then ∑ s', P s (π t s) s' * escapeProb P K T π (t + 1) s' else 1)
      else 0 := by
  rw [escapeProb]

theorem uValue_eq {S A : Type} [Fintype S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (T : ℕ) (π : ℕ → S → A) (t : ℕ) (s : S) :
    uValue P r T π t s =
      if t < T then
        (1 / (T : ℝ)) * r s (π t s) + ∑ s', P s (π t s) s' * uValue P r T π (t + 1) s'
      else 0 := by
  unfold uValue
  rw [SampleComplexityRL.PolicyGrad.tValue]
  by_cases h : t < T
  · simp [h, SampleComplexityRL.Mismeasure.detNSPolicy]
  · simp [h]

theorem uValue_bd {S A : Type} [Fintype S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (hP : IsTransitionKernel P)
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (T : ℕ) (π : ℕ → S → A) (t : ℕ) (s : S) :
    0 ≤ uValue P r T π t s ∧ uValue P r T π t s ≤ ((T - t : ℕ) : ℝ) / T := by
  rw [uValue_eq]
  by_cases h : t < T
  · simp only [h, if_true]
    have ih := fun s' => uValue_bd P r hP hr T π (t + 1) s'
    have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    have hsum : ∀ c : ℝ, ∑ s', P s (π t s) s' * c = c := by
      intro c
      rw [← Finset.sum_mul, (hP s (π t s)).2, one_mul]
    constructor
    · exact add_nonneg (mul_nonneg (by positivity) (hr _ _).1)
        (Finset.sum_nonneg fun s' _ => mul_nonneg ((hP s _).1 s') (ih s').1)
    · calc (1 / (T : ℝ)) * r s (π t s) + ∑ s', P s (π t s) s' * uValue P r T π (t + 1) s'
          ≤ (1 / (T : ℝ)) * 1 + ∑ s', P s (π t s) s' * (((T - (t + 1) : ℕ) : ℝ) / T) := by
            gcongr with s' _
            · exact (hr _ _).2
            · exact (hP s _).1 s'
            · exact (ih s').2
        _ = ((T - t : ℕ) : ℝ) / T := by
            rw [hsum]
            have : ((T - t : ℕ) : ℝ) = 1 + ((T - (t + 1) : ℕ) : ℝ) := by
              have : T - t = 1 + (T - (t + 1)) := by omega
              rw [this]; push_cast; ring
            rw [this]; field_simp
  · have h0 : T - t = 0 := by omega
    simp [h, h0]

theorem uValue_le_one {S A : Type} [Fintype S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (hP : IsTransitionKernel P)
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (T : ℕ) (π : ℕ → S → A) (t : ℕ) (s : S) :
    uValue P r T π t s ≤ 1 := by
  refine (uValue_bd P r hP hr T π t s).2.trans ?_
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0; simp
  · have hTpos : (0 : ℝ) < T := by exact_mod_cast hpos
    rw [div_le_one hTpos]
    exact_mod_cast Nat.sub_le T t

theorem inducedP_kernel {S A : Type} [Fintype S] [DecidableEq S]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (K : Finset S) :
    IsTransitionKernel (inducedP P K) := by
  intro s a
  by_cases hs : s ∈ K
  · simpa [inducedP, hs] using hP s a
  · constructor
    · intro s'; simp only [inducedP, hs, if_false]; split_ifs <;> norm_num
    · simp [inducedP, hs]

theorem inducedR_bd {S A : Type} [DecidableEq S]
    (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (K : Finset S) :
    ∀ s a, 0 ≤ inducedR r K s a ∧ inducedR r K s a ≤ 1 := by
  intro s a
  by_cases hs : s ∈ K
  · simpa [inducedR, hs] using hr s a
  · simp [inducedR, hs]

theorem absorbing {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (K : Finset S) (T : ℕ) (π : ℕ → S → A)
    (t : ℕ) (s : S) (hs : s ∉ K) :
    uValue (inducedP P K) (inducedR r K) T π t s = ((T - t : ℕ) : ℝ) / T := by
  rw [uValue_eq]
  by_cases h : t < T
  · simp only [h, if_true]
    have ih := absorbing P r K T π (t + 1) s hs
    have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    have h1 : ∀ s', inducedP P K s (π t s) s' = if s' = s then 1 else 0 := by
      intro s'; simp [inducedP, hs]
    simp only [h1, inducedR, hs, if_false, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, mul_one]
    rw [ih]
    have : ((T - t : ℕ) : ℝ) = 1 + ((T - (t + 1) : ℕ) : ℝ) := by
      have : T - t = 1 + (T - (t + 1)) := by omega
      rw [this]; push_cast; ring
    rw [this]; field_simp
  · have h0 : T - t = 0 := by omega
    simp [h, h0]
termination_by T - t

theorem induced_core {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (hP : IsTransitionKernel P)
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (K : Finset S) (T : ℕ) (π : ℕ → S → A)
    (t : ℕ) (s : S) :
    uValue P r T π t s ≤ uValue (inducedP P K) (inducedR r K) T π t s ∧
      uValue (inducedP P K) (inducedR r K) T π t s - escapeProb P K T π t s
        ≤ uValue P r T π t s := by
  by_cases h : t < T
  · have ih := fun s' => induced_core P r hP hr K T π (t + 1) s'
    by_cases hs : s ∈ K
    · have hPK : ∀ a s', inducedP P K s a s' = P s a s' := by
        intro a s'; simp [inducedP, hs]
      have hRK : ∀ a, inducedR r K s a = r s a := by
        intro a; simp [inducedR, hs]
      rw [uValue_eq P r, uValue_eq (inducedP P K) (inducedR r K), esc_eq]
      simp only [h, hs, if_true, hPK, hRK]
      have hnn : ∀ s', 0 ≤ P s (π t s) s' := fun s' => (hP s _).1 s'
      constructor
      · have := Finset.sum_le_sum (s := Finset.univ) fun s' _ =>
          mul_le_mul_of_nonneg_left (ih s').1 (hnn s')
        linarith
      · have : ∑ s', P s (π t s) s' * uValue (inducedP P K) (inducedR r K) T π (t + 1) s'
              - ∑ s', P s (π t s) s' * escapeProb P K T π (t + 1) s'
              ≤ ∑ s', P s (π t s) s' * uValue P r T π (t + 1) s' := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_le_sum
          intro s' _
          rw [← mul_sub]
          exact mul_le_mul_of_nonneg_left (by linarith [(ih s').2]) (hnn s')
        linarith
    · have hesc : escapeProb P K T π t s = 1 := by
        rw [esc_eq]; simp [h, hs]
      rw [hesc, absorbing P r K T π t s hs]
      have h1 := uValue_bd P r hP hr T π t s
      have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
      have h2 : ((T - t : ℕ) : ℝ) / T ≤ 1 := by
        rw [div_le_one hTpos]; exact_mod_cast Nat.sub_le T t
      exact ⟨h1.2, by linarith [h1.1]⟩
  · have h0 : uValue P r T π t s = 0 := by rw [uValue_eq]; simp [h]
    have h0' : uValue (inducedP P K) (inducedR r K) T π t s = 0 := by rw [uValue_eq]; simp [h]
    have h0'' : escapeProb P K T π t s = 0 := by rw [esc_eq]; simp [h]
    rw [h0, h0', h0'']; simp
termination_by T - t

theorem implicit_core {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (hP : IsTransitionKernel P)
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (K : Finset S) (T : ℕ) (π : ℕ → S → A)
    (hπ : IsTStepOptimal (inducedP P K) (inducedR r K) T π)
    (t : ℕ) (ht : t < T) (s : S) :
    optUValue P r T t s - escapeProb P K T π t s ≤ uValue P r T π t s := by
  haveI : Nonempty (ℕ → S → A) := ⟨fun _ _ => Classical.arbitrary A⟩
  have hkP := inducedP_kernel P hP K
  have hkR := inducedR_bd r hr K
  have h1 : optUValue P r T t s ≤ uValue (inducedP P K) (inducedR r K) T π t s := by
    rw [hπ t ht s]
    unfold optUValue
    apply ciSup_le
    intro π'
    have hbdd : BddAbove (Set.range fun π'' : ℕ → S → A =>
        uValue (inducedP P K) (inducedR r K) T π'' t s) :=
      ⟨1, by rintro _ ⟨π'', rfl⟩; exact uValue_le_one _ _ hkP hkR T π'' t s⟩
    exact (induced_core P r hP hr K T π' t s).1.trans (le_ciSup hbdd π')
  have h2 := (induced_core P r hP hr K T π t s).2
  linarith

theorem le_opt {S A : Type} [Fintype S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (hP : IsTransitionKernel P)
    (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) (T : ℕ) (π : ℕ → S → A) (t : ℕ) (s : S) :
    uValue P r T π t s ≤ optUValue P r T t s := by
  unfold optUValue
  have hbdd : BddAbove (Set.range fun π'' : ℕ → S → A => uValue P r T π'' t s) :=
    ⟨1, by rintro _ ⟨π'', rfl⟩; exact uValue_le_one _ _ hP hr T π'' t s⟩
  exact le_ciSup hbdd π

theorem det_kernel {S A : Type} [Fintype S] [DecidableEq S] (f : S → A → S) :
    IsTransitionKernel (detKernel f) := by
  intro s a
  constructor
  · intro s'; simp only [detKernel]; split_ifs <;> norm_num
  · simp [detKernel]

theorem det_esc_aux {S A : Type} [Fintype S] [DecidableEq S]
    (f : S → A → S) (K : Finset S) (T : ℕ) (π : ℕ → S → A) (t : ℕ) (s : S) :
    escapeProb (detKernel f) K T π t s = 0 ∨ escapeProb (detKernel f) K T π t s = 1 := by
  rw [esc_eq]
  by_cases h : t < T
  · by_cases hs : s ∈ K
    · simp only [h, hs, if_true, detKernel, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ]
      exact det_esc_aux f K T π (t + 1) _
    · simp [h, hs]
  · simp [h]
termination_by T - t

theorem eps_core {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P Phat : S → A → S → ℝ) (r : S → A → ℝ) (hP : IsTransitionKernel P)
    (hPhat : IsTransitionKernel Phat) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (ε : ℝ) (happrox : IsEpsApprox Phat P ε) (T : ℕ) (π : ℕ → S → A) (k : ℕ) :
    ∀ (t : ℕ) (s : S), t + k + 1 = T →
      |uValue Phat r T π t s - uValue P r T π t s| ≤ ε * k := by
  induction k with
  | zero =>
    intro t s ht
    have h1 : t < T := by omega
    have h2 : ¬ (t + 1 < T) := by omega
    have h3 : ∀ (Q : S → A → S → ℝ) s', uValue Q r T π (t + 1) s' = 0 := by
      intro Q s'; rw [uValue_eq]; simp [h2]
    rw [uValue_eq Phat r, uValue_eq P r]
    simp [h1, h3]
  | succ k ih =>
    intro t s ht
    have h1 : t < T := by omega
    have h2 : t + 1 + k + 1 = T := by omega
    rw [uValue_eq Phat r, uValue_eq P r]
    simp only [h1, if_true]
    set a := π t s
    set u' := fun s' => uValue Phat r T π (t + 1) s' with hu'
    set v' := fun s' => uValue P r T π (t + 1) s' with hv'
    have hb : ∀ s', 0 ≤ u' s' ∧ u' s' ≤ 1 := fun s' =>
      ⟨(uValue_bd Phat r hPhat hr T π (t + 1) s').1, uValue_le_one Phat r hPhat hr T π (t + 1) s'⟩
    have hd : ∀ s', |u' s' - v' s'| ≤ ε * k := fun s' => ih (t + 1) s' h2
    have hdecomp : 1 / (T : ℝ) * r s a + ∑ s', Phat s a s' * u' s' -
        (1 / (T : ℝ) * r s a + ∑ s', P s a s' * v' s') =
        ∑ s', (Phat s a s' - P s a s') * u' s' + ∑ s', P s a s' * (u' s' - v' s') := by
      rw [← Finset.sum_add_distrib]
      have : ∑ s', Phat s a s' * u' s' - ∑ s', P s a s' * v' s' =
          ∑ s', ((Phat s a s' - P s a s') * u' s' + P s a s' * (u' s' - v' s')) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro s' _; ring
      linarith
    show |1 / (T : ℝ) * r s a + ∑ s', Phat s a s' * u' s' -
        (1 / (T : ℝ) * r s a + ∑ s', P s a s' * v' s')| ≤ ε * ((k + 1 : ℕ) : ℝ)
    rw [hdecomp]
    have hA : |∑ s', (Phat s a s' - P s a s') * u' s'| ≤ ε := by
      calc |∑ s', (Phat s a s' - P s a s') * u' s'|
          ≤ ∑ s', |(Phat s a s' - P s a s') * u' s'| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s', |Phat s a s' - P s a s'| := by
            apply Finset.sum_le_sum; intro s' _
            rw [abs_mul]
            have : |u' s'| ≤ 1 := by rw [abs_of_nonneg (hb s').1]; exact (hb s').2
            calc |Phat s a s' - P s a s'| * |u' s'| ≤ |Phat s a s' - P s a s'| * 1 :=
                  mul_le_mul_of_nonneg_left this (abs_nonneg _)
              _ = _ := mul_one _
        _ ≤ ε := (happrox s a).le
    have hB : |∑ s', P s a s' * (u' s' - v' s')| ≤ ε * k := by
      calc |∑ s', P s a s' * (u' s' - v' s')|
          ≤ ∑ s', |P s a s' * (u' s' - v' s')| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s', P s a s' * (ε * k) := by
            apply Finset.sum_le_sum; intro s' _
            rw [abs_mul, abs_of_nonneg ((hP s a).1 s')]
            exact mul_le_mul_of_nonneg_left (hd s') ((hP s a).1 s')
        _ = ε * k := by rw [← Finset.sum_mul, (hP s a).2, one_mul]
    calc _ ≤ |∑ s', (Phat s a s' - P s a s') * u' s'| + |∑ s', P s a s' * (u' s' - v' s')| :=
          abs_add_le _ _
      _ ≤ ε + ε * k := add_le_add hA hB
      _ = ε * ((k + 1 : ℕ) : ℝ) := by push_cast; ring

end SCRAux

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P Phat : S → A → S → ℝ) (r : S → A → ℝ) (hP : IsTransitionKernel P)
    (hPhat : IsTransitionKernel Phat) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (ε : ℝ) (happrox : IsEpsApprox Phat P ε)
    (T : ℕ) (π : ℕ → S → A) (t : ℕ) (ht : t < T) (s : S) :
    |uValue Phat r T π t s - uValue P r T π t s| < ε * T := by
  have hε : 0 < ε := by
    have h0 : 0 ≤ ∑ s', |Phat s (Classical.arbitrary A) s' - P s (Classical.arbitrary A) s'| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact lt_of_le_of_lt h0 (happrox s (Classical.arbitrary A))
  have h := SCRAux.eps_core P Phat r hP hPhat hr ε happrox T π (T - 1 - t) t s (by omega)
  have hk : ((T - 1 - t : ℕ) : ℝ) < T := by
    have : T - 1 - t < T := by omega
    exact_mod_cast this
  calc _ ≤ ε * ((T - 1 - t : ℕ) : ℝ) := h
    _ < ε * T := mul_lt_mul_of_pos_left hk hε
