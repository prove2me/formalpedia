-- Prove2me | solution 1 for QLearning.Convergence.lemmaB4_close_chains_close_values
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:40:44.345694+00:00
-- url     : https://prove2.me/submissions/2b5eaf59-46f3-4ba2-a835-630fdf5ce232

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open QLearning.Convergence

lemma jj_stoch {X : Type} [Fintype X] (p w : X → ℝ) (hp : ∀ y, 0 ≤ p y) (hs : ∑ y, p y = 1)
    (B : ℝ) (hw : ∀ y, |w y| ≤ B) : |∑ y, p y * w y| ≤ B := by
  calc |∑ y, p y * w y| ≤ ∑ y, |p y * w y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, p y * |w y| := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (hp y)]
    _ ≤ ∑ y, p y * B := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hw y) (hp y)
    _ = B := by rw [← Finset.sum_mul, hs, one_mul]

theorem solution {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : FiniteMDP X A) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Rbar : ℝ) (hRbar : 0 < Rbar) (hR : ∀ x a, |M.R x a| ≤ Rbar)
    (Ps : ℕ → X → A → X → ℝ) (Rs : ℕ → X → A → ℝ) (η : ℝ) (hη : 0 < η)
    (bs : List A) (hs : 1 ≤ bs.length)
    (hPs_nonneg : ∀ i, 1 ≤ i → i ≤ bs.length → ∀ x a y, 0 ≤ Ps i x a y)
    (hPs_sum : ∀ i, 1 ≤ i → i ≤ bs.length → ∀ x a, ∑ y, Ps i x a y = 1)
    (hP : ∀ i, 1 ≤ i → i ≤ bs.length → ∀ x a, ∑ y, |Ps i x a y - M.P x a y| < η / Rbar)
    (hRs : ∀ i, 1 ≤ i → i ≤ bs.length → ∀ x a, |Rs i x a - M.R x a| < η) :
    ∀ x, |chainValue Ps Rs γ 1 x bs - seqValue M γ x bs|
      < (bs.length : ℝ) * (bs.length + 1) / 2 * η := by
  have hseq : ∀ (l : List A) (y : X), |seqValue M γ y l| ≤ (l.length : ℝ) * Rbar := by
    intro l
    induction l with
    | nil => intro y; simp
    | cons b l ih =>
      intro y
      rw [seqValue_cons]
      have h1 := jj_stoch (fun z => M.P y b z) (fun z => seqValue M γ z l)
        (fun z => M.P_nonneg _ _ _) (M.P_sum _ _) ((l.length : ℝ) * Rbar) ih
      have h2 : 0 ≤ (l.length : ℝ) * Rbar := by positivity
      calc |M.R y b + γ * ∑ z, M.P y b z * seqValue M γ z l|
          ≤ |M.R y b| + |γ * ∑ z, M.P y b z * seqValue M γ z l| := abs_add_le _ _
        _ ≤ Rbar + γ * ((l.length : ℝ) * Rbar) := by
            rw [abs_mul, abs_of_pos hγ0]
            exact add_le_add (hR y b) (mul_le_mul_of_nonneg_left h1 hγ0.le)
        _ ≤ ((l.length + 1 : ℕ) : ℝ) * Rbar := by
            push_cast
            nlinarith
  set N := bs.length with hN
  have claim : ∀ (m : ℕ) (l : List A), l.length = m → ∀ i : ℕ, 1 ≤ i → i + m ≤ N + 1 → ∀ x : X,
      |chainValue Ps Rs γ i x l - seqValue M γ x l| ≤ (m : ℝ) * (m + 1) / 2 * η ∧
      (0 < m → |chainValue Ps Rs γ i x l - seqValue M γ x l| < (m : ℝ) * (m + 1) / 2 * η) := by
    intro m
    induction m with
    | zero =>
      intro l hl i hi him x
      have : l = [] := List.length_eq_zero_iff.mp hl
      subst this
      simp [chainValue]
    | succ m ih =>
      intro l hl i hi him x
      cases l with
      | nil => simp at hl
      | cons b l' =>
        have hl' : l'.length = m := by simpa using hl
        have ih' := fun y => (ih l' hl' (i + 1) (by omega) (by omega) y).1
        have hi1 : i ≤ N := by omega
        have e : chainValue Ps Rs γ i x (b :: l') - seqValue M γ x (b :: l') =
            (Rs i x b - M.R x b) + γ * (∑ y, Ps i x b y * (chainValue Ps Rs γ (i + 1) y l' - seqValue M γ y l')
              + ∑ y, (Ps i x b y - M.P x b y) * seqValue M γ y l') := by
          rw [seqValue_cons]
          simp only [chainValue, mul_sub, sub_mul, Finset.sum_sub_distrib]
          ring
        have t1 := jj_stoch (fun y => Ps i x b y)
          (fun y => chainValue Ps Rs γ (i + 1) y l' - seqValue M γ y l')
          (fun y => hPs_nonneg i hi hi1 x b y) (hPs_sum i hi hi1 x b)
          ((m : ℝ) * (m + 1) / 2 * η) ih'
        have t2 : |∑ y, (Ps i x b y - M.P x b y) * seqValue M γ y l'| ≤ (m : ℝ) * η := by
          calc |∑ y, (Ps i x b y - M.P x b y) * seqValue M γ y l'|
              ≤ ∑ y, |(Ps i x b y - M.P x b y) * seqValue M γ y l'| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ y, |Ps i x b y - M.P x b y| * ((m : ℝ) * Rbar) := by
                refine Finset.sum_le_sum fun y _ => ?_
                rw [abs_mul]
                have := hseq l' y
                rw [hl'] at this
                exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
            _ = (∑ y, |Ps i x b y - M.P x b y|) * ((m : ℝ) * Rbar) := by rw [Finset.sum_mul]
            _ ≤ (η / Rbar) * ((m : ℝ) * Rbar) := by
                apply mul_le_mul_of_nonneg_right (hP i hi hi1 x b).le
                positivity
            _ = (m : ℝ) * η := by field_simp
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hsum : |∑ y, Ps i x b y * (chainValue Ps Rs γ (i + 1) y l' - seqValue M γ y l')
              + ∑ y, (Ps i x b y - M.P x b y) * seqValue M γ y l'|
            ≤ (m : ℝ) * (m + 1) / 2 * η + (m : ℝ) * η := (abs_add_le _ _).trans (add_le_add t1 t2)
        have hnn : 0 ≤ (m : ℝ) * (m + 1) / 2 * η + (m : ℝ) * η := by positivity
        have hlt : |chainValue Ps Rs γ i x (b :: l') - seqValue M γ x (b :: l')|
            < ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) + 1) / 2 * η := by
          rw [e]
          have ha := hRs i hi hi1 x b
          have hb : |γ * (∑ y, Ps i x b y * (chainValue Ps Rs γ (i + 1) y l' - seqValue M γ y l')
              + ∑ y, (Ps i x b y - M.P x b y) * seqValue M γ y l')|
              ≤ (m : ℝ) * (m + 1) / 2 * η + (m : ℝ) * η := by
            rw [abs_mul, abs_of_pos hγ0]
            calc _ ≤ γ * ((m : ℝ) * (m + 1) / 2 * η + (m : ℝ) * η) :=
                  mul_le_mul_of_nonneg_left hsum hγ0.le
              _ ≤ 1 * ((m : ℝ) * (m + 1) / 2 * η + (m : ℝ) * η) :=
                  mul_le_mul_of_nonneg_right hγ1.le hnn
              _ = _ := one_mul _
          calc _ ≤ |Rs i x b - M.R x b| + |γ * _| := abs_add_le _ _
            _ < η + ((m : ℝ) * (m + 1) / 2 * η + (m : ℝ) * η) := add_lt_add_of_lt_of_le ha hb
            _ = ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) + 1) / 2 * η := by push_cast; ring
        exact ⟨hlt.le, fun _ => hlt⟩
  intro x
  exact (claim N bs rfl 1 le_rfl (by omega) x).2 (by omega)
