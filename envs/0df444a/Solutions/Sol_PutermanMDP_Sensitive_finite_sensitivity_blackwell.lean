-- Prove2me | solution 1 for PutermanMDP.Sensitive.finite_sensitivity_blackwell
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T05:37:20.133987+00:00
-- url     : https://prove2.me/submissions/2ab6d85f-0f0d-4fa7-96a0-1e44481914e0

import Mathlib
import Definitions.Def_PutermanMDP_Sensitive_Model

namespace S226M_08755f3f

open PutermanMDP.Sensitive

def M : Model (Fin 2) (Fin 2) where
  admissible := fun _ => Finset.univ
  admissible_nonempty := fun _ => Finset.univ_nonempty
  reward := fun s a => if s = 0 ∧ a = 1 then 1 else 0
  trans := fun s a t => if s = 0 ∧ a = 0 then (if t = 0 then 1 else 0)
    else (if t = 1 then 1 else 0)
  trans_nonneg := by intros; split_ifs <;> norm_num
  trans_sum := by
    intro s a
    fin_cases s <;> fin_cases a <;> simp [Fin.sum_univ_two]

def dstar : DecisionRule M := ⟨fun _ => 0, fun _ => Finset.mem_univ _⟩
def dB : DecisionRule M := ⟨fun _ => 1, fun _ => Finset.mem_univ _⟩

lemma policyMatrix_dstar : policyMatrix dstar = 1 := by
  funext s t
  fin_cases s <;> fin_cases t <;> simp [policyMatrix, M, dstar]

lemma recClass_iff (C : Finset (Fin 2)) :
    RecurrentClass (1 : Matrix (Fin 2) (Fin 2) ℝ) C ↔ C = {0} ∨ C = {1} := by
  constructor
  · rintro ⟨⟨x, hx⟩, _, hirr⟩
    have hall : ∀ y ∈ C, y = x := by
      intro y hy
      obtain ⟨n, hn⟩ := hirr y hy x hx
      rw [one_pow, Matrix.one_apply] at hn
      split_ifs at hn with h
      · exact h
      · exact absurd hn (lt_irrefl 0)
    have hC : C = {x} := Finset.eq_singleton_iff_unique_mem.2 ⟨hx, hall⟩
    fin_cases x
    · left; exact hC
    · right; exact hC
  · rintro (rfl | rfl)
    · refine ⟨by simp, ?_, ?_⟩
      · intro s hs t ht
        rw [Matrix.one_apply] at ht
        split_ifs at ht with h
        · rw [← h]; exact hs
        · exact absurd ht (lt_irrefl 0)
      · intro s hs t ht
        simp only [Finset.mem_singleton] at hs ht
        subst hs; subst ht
        exact ⟨0, by simp⟩
    · refine ⟨by simp, ?_, ?_⟩
      · intro s hs t ht
        rw [Matrix.one_apply] at ht
        split_ifs at ht with h
        · rw [← h]; exact hs
        · exact absurd ht (lt_irrefl 0)
      · intro s hs t ht
        simp only [Finset.mem_singleton] at hs ht
        subst hs; subst ht
        exact ⟨0, by simp⟩

lemma recCount : recurrentCount (policyMatrix dstar) = 2 := by
  rw [policyMatrix_dstar]
  unfold recurrentCount
  have : {C : Finset (Fin 2) | RecurrentClass (1 : Matrix (Fin 2) (Fin 2) ℝ) C} =
      {{0}, {1}} := by
    ext C
    rw [Set.mem_setOf_eq, recClass_iff]
    simp
  rw [this, Set.ncard_pair]
  decide

lemma ER_nonneg (π : Policy M) : ∀ n h s, 0 ≤ expectedReward π n h s := by
  intro n
  induction n with
  | zero =>
    intro h s
    simp only [expectedReward]
    apply Finset.sum_nonneg
    intro a _
    apply mul_nonneg (π.nonneg _ _ _ _)
    simp only [M]; split_ifs <;> norm_num
  | succ n ih =>
    intro h s
    simp only [expectedReward]
    apply Finset.sum_nonneg
    intro a _
    apply mul_nonneg (π.nonneg _ _ _ _)
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (M.trans_nonneg _ _ _) (ih _ _)

lemma ER_one (π : Policy M) : ∀ n h, expectedReward π n h 1 = 0 := by
  intro n
  induction n with
  | zero => intro h; simp [expectedReward, M]
  | succ n ih =>
    intro h
    simp only [expectedReward]
    apply Finset.sum_eq_zero
    intro a _
    have : ∑ t, M.trans 1 a t * expectedReward π n (h ++ [(1, a)]) t = 0 := by
      simp [M]
      exact ih _
    rw [this, mul_zero]

lemma qsum (π : Policy M) (t : ℕ) (h : List (Fin 2 × Fin 2)) (s : Fin 2) :
    π.q t h s 0 + π.q t h s 1 = 1 := by
  have := π.sum_one t h s
  simpa [M, Fin.sum_univ_two] using this

lemma ER_zero_succ (π : Policy M) (k : ℕ) (h : List (Fin 2 × Fin 2)) :
    expectedReward π (k + 1) h 0 =
      π.q h.length h 0 0 * expectedReward π k (h ++ [(0, 0)]) 0 := by
  simp only [expectedReward]
  change ∑ a ∈ Finset.univ, _ = _
  simp [Fin.sum_univ_two, M]
  right; exact ER_one π k _

lemma ER_zero_zero (π : Policy M) (h : List (Fin 2 × Fin 2)) :
    expectedReward π 0 h 0 = π.q h.length h 0 1 := by
  simp only [expectedReward]
  change ∑ a ∈ Finset.univ, _ = _
  simp [Fin.sum_univ_two, M]

lemma ER_sum (π : Policy M) : ∀ n h,
    ∑ k ∈ Finset.range (n + 1), expectedReward π k h 0 ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro h
    rw [Finset.sum_range_one, ER_zero_zero]
    have := qsum π h.length h 0
    have := π.nonneg h.length h 0 0
    linarith
  | succ n ih =>
    intro h
    rw [Finset.sum_range_succ', ER_zero_zero]
    simp only [ER_zero_succ]
    rw [← Finset.mul_sum]
    have h1 := ih (h ++ [(0, 0)])
    have h2 := qsum π h.length h 0
    have h3 := π.nonneg h.length h 0 0
    nlinarith

lemma value_le (π : Policy M) (β : ℝ) (h0 : 0 ≤ β) (h1 : β < 1) (s : Fin 2) :
    value π β s ≤ 1 := by
  unfold value
  apply Real.tsum_le_of_sum_range_le
  · intro n; exact mul_nonneg (pow_nonneg h0 _) (ER_nonneg π _ _ _)
  · intro n
    fin_cases s
    · rcases n with _ | n
      · simp
      · calc ∑ i ∈ Finset.range (n + 1), β ^ i * expectedReward π i [] 0
            ≤ ∑ i ∈ Finset.range (n + 1), expectedReward π i [] 0 := by
              apply Finset.sum_le_sum
              intro i _
              have := ER_nonneg π i [] 0
              have : β ^ i ≤ 1 := pow_le_one₀ h0 h1.le
              nlinarith
          _ ≤ 1 := ER_sum π n []
    · simp [ER_one]

lemma ER_dstar : ∀ n h s, expectedReward (stationary dstar) n h s = 0 := by
  intro n
  induction n with
  | zero =>
    intro h s
    simp only [expectedReward]
    apply Finset.sum_eq_zero
    intro a _
    fin_cases a <;> simp [stationary, MarkovDecisionProcesses.stationaryPolicy, dstar, M]
  | succ n ih =>
    intro h s
    simp [expectedReward, ih]

lemma value_dstar (β : ℝ) (s : Fin 2) : value (stationary dstar) β s = 0 := by
  simp [value, ER_dstar]

lemma value_dB (β : ℝ) : value (stationary dB) β 0 = 1 := by
  unfold value
  rw [tsum_eq_single 0]
  · rw [ER_zero_zero]
    simp [stationary, MarkovDecisionProcesses.stationaryPolicy, dB]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [ER_zero_succ]
    simp [stationary, MarkovDecisionProcesses.stationaryPolicy, dB]

lemma hopt : NDiscountOptimal (stationary dstar)
    ((Fintype.card (Fin 2) : ℤ) - ((2 : ℕ) : ℤ) - 1) := by
  have : ((Fintype.card (Fin 2) : ℤ) - ((2 : ℕ) : ℤ) - 1) = -1 := by simp
  rw [this]
  refine ⟨le_refl _, fun π s ε hε => ⟨max 0 (1 - ε), le_max_left _ _,
    max_lt (by norm_num) (by linarith), fun β hβ0 hβ1 => ?_⟩⟩
  rw [neg_neg, zpow_one, value_dstar]
  have hb0 : 0 ≤ β := le_trans (le_max_left _ _) hβ0
  have hb1 : 1 - ε ≤ β := le_trans (le_max_right _ _) hβ0
  have hv := value_le π β hb0 hβ1 s
  nlinarith

end S226M_08755f3f

open PutermanMDP.Sensitive in
theorem solution : ¬ (∀ {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    (M : Model S A) (dstar : DecisionRule M) (r : ℕ)
    (hopt : NDiscountOptimal (stationary dstar) ((Fintype.card S : ℤ) - (r : ℤ) - 1))
    (hr : recurrentCount (policyMatrix dstar) = r),
    BlackwellOptimal (stationary dstar) ∧
      ∀ n : ℤ, -1 ≤ n → NDiscountOptimal (stationary dstar) n) := by
  intro H
  obtain ⟨⟨β0, h0, h1, hB⟩, _⟩ := H S226M_08755f3f.M S226M_08755f3f.dstar 2
    S226M_08755f3f.hopt S226M_08755f3f.recCount
  have := hB β0 le_rfl h1 (stationary S226M_08755f3f.dB) 0
  rw [S226M_08755f3f.value_dB, S226M_08755f3f.value_dstar] at this
  norm_num at this
