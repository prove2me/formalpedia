-- Prove2me | solution 1 for QFlexSC.ZeroInv.inventory_nonincreasing
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:30:20.754991+00:00
-- url     : https://prove2.me/submissions/59939b26-7bc0-4475-9aae-cafc073888fa

import Theorems.Thm_QFlexSC_ZeroInv_coverage

set_option autoImplicit false
open QFlexSC.ZeroInv

private theorem down_nonneg (ω : ℕ → ℝ) (hω : ∀ q, 1 ≤ q → ω q ≤ 1) (j : ℕ) :
    0 ≤ 1 - Ωcum ω j := by
  simp only [Ωcum, sub_sub_cancel]
  exact Finset.prod_nonneg (fun q hq => sub_nonneg.mpr (hω q (Finset.mem_Icc.mp hq).1))

private theorem down_succ (ω : ℕ → ℝ) (j : ℕ) :
    1 - Ωcum ω (j + 1) = (1 - Ωcum ω j) * (1 - ω (j + 1)) := by
  simp only [Ωcum, sub_sub_cancel, Finset.prod_Icc_succ_top (by omega : 1 ≤ j + 1)]

private theorem up_pos (α : ℕ → ℝ) (hα : ∀ q, 1 ≤ q → 0 ≤ α q) (j : ℕ) :
    0 < 1 + Acum α j := by
  have h := Finset.prod_pos (s := Finset.Icc 1 j) (f := fun q => 1 + α q)
    (fun q hq => by linarith [hα q (Finset.mem_Icc.mp hq).1])
  unfold Acum
  linarith

private theorem project_nonneg (P : QFParams) (Iprev : ℝ) (rprev f : ℕ → ℝ)
    (hI : 0 ≤ Iprev) (j : ℕ) : 0 ≤ proj P Iprev rprev f j := by
  cases j with
  | zero => exact hI
  | succ j => exact le_max_left _ _

private theorem target_bound (P : QFParams) (f : ℕ → ℝ) (l : ℝ) (j : ℕ)
    (hin : ∀ q, 1 ≤ q → 0 ≤ P.αin q)
    (hA : Acum P.αout j ≤ Acum P.αin j) (hl : 0 ≤ l) (hf : 0 ≤ f j) :
    target P f l j ≤ f j := by
  unfold target
  apply (div_le_iff₀ (up_pos P.αin hin j)).2
  have h := mul_le_mul_of_nonneg_right (show 1 + Acum P.αout j ≤ 1 + Acum P.αin j by linarith) hf
  nlinarith only [h, hl]

private theorem weighted_schedule (P : QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ)
    (hstd : ∀ q, 1 ≤ q → 0 ≤ P.αin q ∧ 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1 ∧
      0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (hf : ∀ t j, 0 ≤ f t j) (hIR : IROut P f) (hI₀ : 0 ≤ I₀) (hr₀ : r₀ = f 0)
    (hd : ∀ j, 1 ≤ j → Acum P.αout j ≤ Acum P.αin j ∧ Ωcum P.ωout j ≤ Ωcum P.ωin j) :
    ∀ t j, (1 - Ωcum P.ωin j) * sched P I₀ r₀ f t j ≤
      (1 - Ωcum P.ωout j) * f t j := by
  have hin (q : ℕ) (hq : 1 ≤ q) : 0 ≤ P.αin q := (hstd q hq).1
  have hdin (j : ℕ) : 0 ≤ 1 - Ωcum P.ωin j :=
    down_nonneg P.ωin (fun q hq => (hstd q hq).2.2.2.1) j
  have hdout (j : ℕ) : 0 ≤ 1 - Ωcum P.ωout j :=
    down_nonneg P.ωout (fun q hq => (hstd q hq).2.2.2.2.2) j
  have hA (j : ℕ) : Acum P.αout j ≤ Acum P.αin j := by
    cases j with
    | zero => simp [Acum]
    | succ j => exact (hd (j + 1) (by omega)).1
  have hcoeff (j : ℕ) : 1 - Ωcum P.ωin j ≤ 1 - Ωcum P.ωout j := by
    cases j with
    | zero => simp [Ωcum]
    | succ j => linarith [(hd (j + 1) (by omega)).2]
  have hstock (t : ℕ) : 0 ≤ inv P I₀ r₀ f t := by
    cases t with
    | zero => exact hI₀
    | succ t => exact (coverage P f I₀ r₀ (t + 1) (by omega)).2
  intro t
  induction t with
  | zero =>
      intro j
      change (1 - Ωcum P.ωin j) * r₀ j ≤ (1 - Ωcum P.ωout j) * f 0 j
      rw [hr₀]
      exact mul_le_mul_of_nonneg_right (hcoeff j) (hf 0 j)
  | succ t ih =>
      intro j
      have hp := project_nonneg P (inv P I₀ r₀ f t) (sched P I₀ r₀ f t) (f (t + 1)) (hstock t) j
      have ht := target_bound P (f (t + 1))
        (proj P (inv P I₀ r₀ f t) (sched P I₀ r₀ f t) (f (t + 1)) j) j hin (hA j) hp (hf (t + 1) j)
      rw [sched_succ]
      unfold mcStep entry
      rw [mul_max_of_nonneg _ _ (hdin j)]
      apply max_le
      · exact (mul_le_mul_of_nonneg_left ht (hdin j)).trans
          (mul_le_mul_of_nonneg_right (hcoeff j) (hf (t + 1) j))
      · calc
          (1 - Ωcum P.ωin j) * ((1 - P.ωin (j + 1)) * sched P I₀ r₀ f t (j + 1)) =
              (1 - Ωcum P.ωin (j + 1)) * sched P I₀ r₀ f t (j + 1) := by rw [down_succ]; ring
          _ ≤ (1 - Ωcum P.ωout (j + 1)) * f t (j + 1) := ih (j + 1)
          _ = (1 - Ωcum P.ωout j) * ((1 - P.ωout (j + 1)) * f t (j + 1)) := by rw [down_succ]; ring
          _ ≤ (1 - Ωcum P.ωout j) * f (t + 1) j :=
            mul_le_mul_of_nonneg_left (hIR t j).1 (hdout j)

theorem solution (P : QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ)
    (hstd : ∀ q, 1 ≤ q → 0 ≤ P.αin q ∧ 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1 ∧
      0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (hf : ∀ t j, 0 ≤ f t j)
    (hIR : IROut P f)
    (hI₀ : 0 ≤ I₀)
    (hr₀ : r₀ = f 0)
    (hd : ∀ j, 1 ≤ j → Acum P.αout j ≤ Acum P.αin j ∧ Ωcum P.ωout j ≤ Ωcum P.ωin j) :
    ∀ t : ℕ, 1 ≤ t →
      sched P I₀ r₀ f t 0 ≤ f t 0 ∧ inv P I₀ r₀ f t ≤ inv P I₀ r₀ f (t - 1) := by
  intro t ht
  have hw := weighted_schedule P f I₀ r₀ hstd hf hIR hI₀ hr₀ hd t 0
  simp [Ωcum] at hw
  refine ⟨hw, ?_⟩
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  rw [inv_succ]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hw ⊢
  linarith

#print axioms solution
