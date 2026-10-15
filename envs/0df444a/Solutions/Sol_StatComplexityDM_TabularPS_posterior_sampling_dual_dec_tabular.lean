-- Prove2me | solution 1 for StatComplexityDM.TabularPS.posterior_sampling_dual_dec_tabular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T04:32:02.278979+00:00
-- url     : https://prove2.me/submissions/e081a3ff-5a56-4536-af06-42d926e9202f

import Mathlib
import Definitions.Def_StatComplexityDM_TabularPS_MDP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PCIGWAux

open StatComplexityDM.TabularPS StatComplexityDM.LowerBound FoundationsRL.GeneralDM

universe u1 u2 u3

variable {S : Type u1} {A : Type u2} {W : Type u3}

/-- drop the first layer -/
def shiftM {n : ℕ} (M : TabMDP S A W (n + 1)) : TabMDP S A W n :=
  ⟨fun h => M.P h.succ, fun h => M.R h.succ⟩

def shiftPi {n : ℕ} (π : Policy S A (n + 1)) : Policy S A n := fun h => π h.succ

theorem nextWeight_cons_succ {n : ℕ} (M : TabMDP S A W (n + 1)) (x : S × A × W)
    (τ : Traj S A W n) (j : Fin n) :
    nextWeight M (Fin.cons (α := fun _ => S × A × W) x τ : Traj S A W (n + 1)) j.succ =
      nextWeight (shiftM M) τ j := by
  unfold nextWeight
  by_cases hj : j.val + 1 < n
  · have h1 : j.succ.val + 1 < n + 1 := by simp; omega
    rw [dif_pos h1, dif_pos hj]
    simp only [shiftM, Fin.val_succ, Fin.cons_succ]
    have e : (Fin.cons (α := fun _ => S × A × W) x τ : Traj S A W (n + 1))
        ⟨j.val + 1 + 1, by omega⟩ = τ ⟨j.val + 1, hj⟩ :=
      Fin.cons_succ (α := fun _ => S × A × W) x τ ⟨j.val + 1, hj⟩
    rw [e]
  · have h1 : ¬ (j.succ.val + 1 < n + 1) := by simp; omega
    rw [dif_neg h1, dif_neg hj]

/-- the peel identity -/
theorem trajLaw_cons {n : ℕ} (d1 : S → ℝ) (M : TabMDP S A W (n + 1)) (π : Policy S A (n + 1))
    (x : S × A × W) (τ : Traj S A W n) :
    trajLaw d1 M π (Fin.cons (α := fun _ => S × A × W) x τ) =
      d1 x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2 *
        trajLaw (fun s' => M.P 0 x.1 x.2.1 s') (shiftM M) (shiftPi π) τ := by
  cases n with
  | zero =>
    simp [trajLaw, nextWeight]
  | succ m =>
    unfold trajLaw
    rw [Fin.prod_univ_succ (n := m + 1)]
    have hterm : ∀ j : Fin (m + 1),
        ((if j.val = 0 then M.P 0 x.1 x.2.1 (τ j).1 else 1) * shiftPi π j (τ j).1 (τ j).2.1 *
          (shiftM M).R j (τ j).1 (τ j).2.1 (τ j).2.2 * nextWeight (shiftM M) τ j) =
        (if j.val = 0 then M.P 0 x.1 x.2.1 (τ j).1 else 1) *
        ((if (j.succ).val = 0 then d1 (Fin.cons (α := fun _ => S × A × W) x τ j.succ).1 else 1) *
          π j.succ (Fin.cons (α := fun _ => S × A × W) x τ j.succ).1
            (Fin.cons (α := fun _ => S × A × W) x τ j.succ).2.1 *
          M.R j.succ (Fin.cons (α := fun _ => S × A × W) x τ j.succ).1
            (Fin.cons (α := fun _ => S × A × W) x τ j.succ).2.1
            (Fin.cons (α := fun _ => S × A × W) x τ j.succ).2.2 *
          nextWeight M (Fin.cons (α := fun _ => S × A × W) x τ : Traj S A W (m + 1 + 1)) j.succ) := by
      intro j
      rw [nextWeight_cons_succ]
      simp only [Fin.cons_succ, shiftPi, shiftM, Fin.val_succ]
      have : (j.val + 1 = 0) = False := by simp
      simp only [this, if_false, one_mul]
      ring
    have hR : ∏ j : Fin (m + 1),
        ((if j.val = 0 then M.P 0 x.1 x.2.1 (τ j).1 else 1) * shiftPi π j (τ j).1 (τ j).2.1 *
          (shiftM M).R j (τ j).1 (τ j).2.1 (τ j).2.2 * nextWeight (shiftM M) τ j) =
        M.P 0 x.1 x.2.1 (τ 0).1 * ∏ j : Fin (m + 1),
        ((if (j.succ).val = 0 then d1 (Fin.cons (α := fun _ => S × A × W) x τ j.succ).1 else 1) *
          π j.succ (Fin.cons (α := fun _ => S × A × W) x τ j.succ).1
            (Fin.cons (α := fun _ => S × A × W) x τ j.succ).2.1 *
          M.R j.succ (Fin.cons (α := fun _ => S × A × W) x τ j.succ).1
            (Fin.cons (α := fun _ => S × A × W) x τ j.succ).2.1
            (Fin.cons (α := fun _ => S × A × W) x τ j.succ).2.2 *
          nextWeight M (Fin.cons (α := fun _ => S × A × W) x τ : Traj S A W (m + 1 + 1)) j.succ) := by
      rw [Finset.prod_congr rfl (fun j _ => hterm j), Finset.prod_mul_distrib]
      congr 1
      rw [Fin.prod_univ_succ]
      simp
    rw [hR]
    have h0 : (Fin.cons (α := fun _ => S × A × W) x τ : Traj S A W (m + 1 + 1))
        ⟨(0 : Fin (m + 1 + 1)).val + 1, by simp⟩ = τ 0 :=
      Fin.cons_succ (α := fun _ => S × A × W) x τ 0
    simp only [nextWeight, Fin.cons_zero]
    rw [dif_pos (show (0 : Fin (m + 1 + 1)).val + 1 < m + 1 + 1 by simp), h0]
    simp only [Fin.val_zero, if_true]
    ring

section fin
variable [Fintype S] [Fintype A] [Fintype W]

theorem sum_traj_succ {n : ℕ} (F : Traj S A W (n + 1) → ℝ) :
    ∑ τ : Traj S A W (n + 1), F τ =
      ∑ x : S × A × W, ∑ τ' : Traj S A W n, F (Fin.cons (α := fun _ => S × A × W) x τ') := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => S × A × W)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem exists_cons {n : ℕ} (τ : Traj S A W (n + 1)) :
    ∃ (x : S × A × W) (τ' : Traj S A W n), τ = Fin.cons (α := fun _ => S × A × W) x τ' :=
  ⟨τ 0, Fin.tail τ, (Fin.cons_self_tail τ).symm⟩

theorem isTab_shift {n : ℕ} {M : TabMDP S A W (n + 1)} (h : IsTabMDP M) : IsTabMDP (shiftM M) :=
  ⟨fun j s a => h.1 j.succ s a, fun j s a => h.2 j.succ s a⟩

theorem isPolicy_shift {n : ℕ} {π : Policy S A (n + 1)} (h : IsPolicy π) : IsPolicy (shiftPi π) :=
  fun j s => h j.succ s

theorem isDist_P {n : ℕ} {M : TabMDP S A W n} (h : IsTabMDP M) (j : Fin n) (s : S) (a : A) :
    IsDist (M.P j s a) := h.1 j s a

/-- Probability-vector property of the trajectory law. -/
theorem trajLaw_prob : ∀ (n : ℕ) (d1 : S → ℝ) (M : TabMDP S A W n) (π : Policy S A n),
    IsDist d1 → IsTabMDP M → IsPolicy π →
    (∀ τ, 0 ≤ trajLaw d1 M π τ) ∧ ∑ τ, trajLaw d1 M π τ = 1 := by
  intro n
  induction n with
  | zero =>
    intro d1 M π _ _ _
    simp [trajLaw]
  | succ n ih =>
    intro d1 M π hd hM hπ
    have hih := fun x : S × A × W => ih (fun s' => M.P 0 x.1 x.2.1 s') (shiftM M) (shiftPi π)
      (hM.1 0 x.1 x.2.1) (isTab_shift hM) (isPolicy_shift hπ)
    have hx : ∀ x : S × A × W, 0 ≤ d1 x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2 :=
      fun x => mul_nonneg (mul_nonneg (hd.1 _) ((hπ 0 x.1).1 _)) ((hM.2 0 x.1 x.2.1).1 _)
    constructor
    · intro τ
      obtain ⟨x, τ', rfl⟩ := exists_cons τ
      rw [trajLaw_cons]
      exact mul_nonneg (hx x) ((hih x).1 τ')
    · rw [sum_traj_succ]
      simp_rw [trajLaw_cons, ← Finset.mul_sum, (fun x => (hih x).2), mul_one]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      have h1 : ∀ s : S, ∑ a : A, ∑ w : W, d1 s * π 0 s a * M.R 0 s a w = d1 s := by
        intro s
        have : ∀ a : A, ∑ w : W, d1 s * π 0 s a * M.R 0 s a w = d1 s * π 0 s a := by
          intro a
          rw [← Finset.mul_sum, (hM.2 0 s a).2, mul_one]
        simp_rw [this]
        rw [← Finset.mul_sum, (hπ 0 s).2, mul_one]
      simp_rw [h1]
      exact hd.2

open Classical in
theorem occ_eq {n : ℕ} (d1 : S → ℝ) (M : TabMDP S A W n) (π : Policy S A n) (h : Fin n)
    (s : S) (a : A) :
    occ d1 M π h s a = ∑ τ : Traj S A W n,
      if (τ h).1 = s ∧ (τ h).2.1 = a then trajLaw d1 M π τ else 0 := by
  unfold occ
  rfl

open Classical in
theorem occ_zero {n : ℕ} (d1 : S → ℝ) (M : TabMDP S A W (n + 1)) (π : Policy S A (n + 1))
    (hd : IsDist d1) (hM : IsTabMDP M) (hπ : IsPolicy π) (s : S) (a : A) :
    occ d1 M π 0 s a = d1 s * π 0 s a := by
  rw [occ_eq, sum_traj_succ]
  have h1 : ∀ x : S × A × W, ∑ τ' : Traj S A W n,
      (if ((Fin.cons (α := fun _ => S × A × W) x τ' : Traj S A W (n + 1)) 0).1 = s ∧
        ((Fin.cons (α := fun _ => S × A × W) x τ' : Traj S A W (n + 1)) 0).2.1 = a then
        trajLaw d1 M π (Fin.cons (α := fun _ => S × A × W) x τ') else 0) =
      if x.1 = s ∧ x.2.1 = a then d1 x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2 else 0 := by
    intro x
    have hih := (trajLaw_prob n (fun s' => M.P 0 x.1 x.2.1 s') (shiftM M) (shiftPi π)
      (hM.1 0 x.1 x.2.1) (isTab_shift hM) (isPolicy_shift hπ)).2
    simp only [Fin.cons_zero, trajLaw_cons]
    split_ifs
    · rw [← Finset.mul_sum, hih, mul_one]
    · simp
  simp_rw [h1]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have h2 : ∀ x y, ∑ z : W, (if x = s ∧ y = a then d1 x * π 0 x y * M.R 0 x y z else 0) =
      if x = s ∧ y = a then d1 x * π 0 x y else 0 := by
    intro x y
    split_ifs
    · rw [← Finset.mul_sum, (hM.2 0 x y).2, mul_one]
    · simp
  simp_rw [h2]
  rw [Finset.sum_eq_single s]
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro b _ hb; simp [hb]
  · simp

open Classical in
theorem occ_succ {n : ℕ} (d1 : S → ℝ) (M : TabMDP S A W (n + 1)) (π : Policy S A (n + 1))
    (h : Fin n) (s : S) (a : A) :
    occ d1 M π h.succ s a = ∑ x : S × A × W, d1 x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2 *
      occ (fun s' => M.P 0 x.1 x.2.1 s') (shiftM M) (shiftPi π) h s a := by
  rw [occ_eq, sum_traj_succ]
  apply Finset.sum_congr rfl
  intro x _
  rw [occ_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ' _
  simp only [Fin.cons_succ, trajLaw_cons]
  split_ifs
  · rfl
  · simp

open Classical in
theorem occ_nonneg {n : ℕ} (d1 : S → ℝ) (M : TabMDP S A W n) (π : Policy S A n)
    (hd : IsDist d1) (hM : IsTabMDP M) (hπ : IsPolicy π) (h : Fin n) (s : S) (a : A) :
    0 ≤ occ d1 M π h s a := by
  rw [occ_eq]
  apply Finset.sum_nonneg
  intro τ _
  split_ifs
  · exact (trajLaw_prob n d1 M π hd hM hπ).1 τ
  · exact le_refl _

open Classical in
theorem occ_sum {n : ℕ} (d1 : S → ℝ) (M : TabMDP S A W n) (π : Policy S A n)
    (hd : IsDist d1) (hM : IsTabMDP M) (hπ : IsPolicy π) (h : Fin n) :
    ∑ s : S, ∑ a : A, occ d1 M π h s a = 1 := by
  simp_rw [occ_eq]
  have : ∀ τ : Traj S A W n, ∑ s : S, ∑ a : A,
      (if (τ h).1 = s ∧ (τ h).2.1 = a then trajLaw d1 M π τ else 0) = trajLaw d1 M π τ := by
    intro τ
    rw [Finset.sum_eq_single (τ h).1]
    · rw [Finset.sum_eq_single (τ h).2.1]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [Finset.sum_congr rfl (fun s _ => Finset.sum_comm), Finset.sum_comm]
  simp_rw [this]
  exact (trajLaw_prob n d1 M π hd hM hπ).2

end fin

/-! ### real-analysis helpers -/

theorem real_ineq (u v t : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht0 : 0 ≤ t) (ht : t ≤ 2) :
    v ^ 2 * t / 2 ≤ (u - v) ^ 2 + u * v * t := by
  nlinarith [sq_nonneg (u - v * (1 - t / 2)), mul_nonneg (mul_nonneg ht0 (sub_nonneg.2 ht)) (sq_nonneg v)]

section aff
variable {Y : Type*} [Fintype Y]

/-- Hellinger affinity -/
noncomputable def aff (f g : Y → ℝ) : ℝ := ∑ y, Real.sqrt (f y) * Real.sqrt (g y)

theorem hellingerSq_eq (f g : Y → ℝ) (hf : IsDist f) (hg : IsDist g) :
    hellingerSq f g = 2 - 2 * aff f g := by
  unfold hellingerSq aff
  have : ∀ y, (Real.sqrt (f y) - Real.sqrt (g y)) ^ 2 =
      f y + g y - 2 * (Real.sqrt (f y) * Real.sqrt (g y)) := by
    intro y
    have h1 := Real.sq_sqrt (hf.1 y)
    have h2 := Real.sq_sqrt (hg.1 y)
    nlinarith
  simp_rw [this]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hf.2, hg.2]
  ring

theorem aff_nonneg (f g : Y → ℝ) : 0 ≤ aff f g :=
  Finset.sum_nonneg (fun y _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem hellingerSq_nonneg' (f g : Y → ℝ) : 0 ≤ hellingerSq f g :=
  Finset.sum_nonneg (fun y _ => sq_nonneg _)

theorem aff_le_one (f g : Y → ℝ) (hf : IsDist f) (hg : IsDist g) : aff f g ≤ 1 := by
  have := hellingerSq_nonneg' f g
  rw [hellingerSq_eq f g hf hg] at this
  linarith

end aff

/-- one-step Hellinger lower bound for a product of two kernels -/
theorem one_step {Y Z : Type*} [Fintype Y] [Fintype Z] (f f' : Y → ℝ) (g g' : Z → ℝ)
    (hf : IsDist f) (hf' : IsDist f') (hg : IsDist g) (hg' : IsDist g') (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    v ^ 2 * (hellingerSq f f' + hellingerSq g g') / 4 ≤
      ∑ y, ∑ z, (u * Real.sqrt (f y * g z) - v * Real.sqrt (f' y * g' z)) ^ 2 := by
  have hS : ∀ (a : Y → ℝ) (b : Z → ℝ), ∑ y, ∑ z, a y * b z = (∑ y, a y) * (∑ z, b z) :=
    fun a b => (Finset.sum_mul_sum _ _ _ _).symm
  have e : ∑ y, ∑ z, (u * Real.sqrt (f y * g z) - v * Real.sqrt (f' y * g' z)) ^ 2 =
      u ^ 2 + v ^ 2 - 2 * u * v * (aff f f' * aff g g') := by
    have h1 : ∀ y z, (u * Real.sqrt (f y * g z) - v * Real.sqrt (f' y * g' z)) ^ 2 =
        u ^ 2 * (f y * g z) + v ^ 2 * (f' y * g' z) -
          2 * u * v * ((Real.sqrt (f y) * Real.sqrt (f' y)) * (Real.sqrt (g z) * Real.sqrt (g' z))) := by
      intro y z
      rw [Real.sqrt_mul (hf.1 y), Real.sqrt_mul (hf'.1 y)]
      have a1 := Real.sq_sqrt (hf.1 y)
      have a2 := Real.sq_sqrt (hf'.1 y)
      have a3 := Real.sq_sqrt (hg.1 z)
      have a4 := Real.sq_sqrt (hg'.1 z)
      calc _ = u ^ 2 * (Real.sqrt (f y) ^ 2 * Real.sqrt (g z) ^ 2) +
            v ^ 2 * (Real.sqrt (f' y) ^ 2 * Real.sqrt (g' z) ^ 2) -
            2 * u * v * ((Real.sqrt (f y) * Real.sqrt (f' y)) * (Real.sqrt (g z) * Real.sqrt (g' z))) := by ring
        _ = _ := by rw [a1, a2, a3, a4]
    simp_rw [h1]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [← Finset.sum_mul, hf.2, hg.2, hf'.2, hg'.2]
    unfold aff
    ring
  rw [e, hellingerSq_eq f f' hf hf', hellingerSq_eq g g' hg hg']
  have a1 := aff_nonneg f f'
  have a2 := aff_nonneg g g'
  have b1 := aff_le_one f f' hf hf'
  have b2 := aff_le_one g g' hg hg'
  have key := real_ineq u v ((1 - aff f f') + (1 - aff g g')) hu hv (by linarith) (by linarith)
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have : 0 ≤ u * v * (aff f f' * (1 - aff g g') + aff g g' * (1 - aff f f')) :=
    mul_nonneg huv (add_nonneg (mul_nonneg a1 (by linarith)) (mul_nonneg a2 (by linarith)))
  nlinarith

/-- one-step bound with a single kernel -/
theorem one_step' {Y : Type*} [Fintype Y] (f f' : Y → ℝ)
    (hf : IsDist f) (hf' : IsDist f') (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    v ^ 2 * hellingerSq f f' / 4 ≤ ∑ y, (u * Real.sqrt (f y) - v * Real.sqrt (f' y)) ^ 2 := by
  have e : ∑ y, (u * Real.sqrt (f y) - v * Real.sqrt (f' y)) ^ 2 =
      u ^ 2 + v ^ 2 - 2 * u * v * aff f f' := by
    have h1 : ∀ y, (u * Real.sqrt (f y) - v * Real.sqrt (f' y)) ^ 2 =
        u ^ 2 * f y + v ^ 2 * f' y - 2 * u * v * (Real.sqrt (f y) * Real.sqrt (f' y)) := by
      intro y
      have a1 := Real.sq_sqrt (hf.1 y)
      have a2 := Real.sq_sqrt (hf'.1 y)
      calc _ = u ^ 2 * Real.sqrt (f y) ^ 2 + v ^ 2 * Real.sqrt (f' y) ^ 2 -
            2 * u * v * (Real.sqrt (f y) * Real.sqrt (f' y)) := by ring
        _ = _ := by rw [a1, a2]
    simp_rw [h1]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hf.2, hf'.2]
    unfold aff
    ring
  rw [e, hellingerSq_eq f f' hf hf']
  have a1 := aff_nonneg f f'
  have b1 := aff_le_one f f' hf hf'
  have key := real_ineq u v (1 - aff f f') hu hv (by linarith) (by linarith)
  nlinarith

theorem sqdiff_eq {Y : Type*} [Fintype Y] (f f' : Y → ℝ) (hf : IsDist f) (hf' : IsDist f')
    (u v : ℝ) :
    ∑ y, (u * Real.sqrt (f y) - v * Real.sqrt (f' y)) ^ 2 =
      u ^ 2 + v ^ 2 - 2 * u * v * aff f f' := by
  have h1 : ∀ y, (u * Real.sqrt (f y) - v * Real.sqrt (f' y)) ^ 2 =
      u ^ 2 * f y + v ^ 2 * f' y - 2 * u * v * (Real.sqrt (f y) * Real.sqrt (f' y)) := by
    intro y
    have a1 := Real.sq_sqrt (hf.1 y)
    have a2 := Real.sq_sqrt (hf'.1 y)
    calc _ = u ^ 2 * Real.sqrt (f y) ^ 2 + v ^ 2 * Real.sqrt (f' y) ^ 2 -
          2 * u * v * (Real.sqrt (f y) * Real.sqrt (f' y)) := by ring
      _ = _ := by rw [a1, a2]
  simp_rw [h1]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hf.2, hf'.2]
  unfold aff
  ring

/-- marginalising a fibred sum onto the base -/
theorem marg_abstract {T : Type*} [Fintype S] [Fintype T] [DecidableEq S] (σ : T → S) (K K' : T → ℝ)
    (hK : ∀ t, 0 ≤ K t) (hK' : ∀ t, 0 ≤ K' t)
    (hs : ∀ s, ∑ t, (if σ t = s then K t else 0) = 1)
    (hs' : ∀ s, ∑ t, (if σ t = s then K' t else 0) = 1)
    (d d' : S → ℝ) (hd : ∀ s, 0 ≤ d s) (hd' : ∀ s, 0 ≤ d' s) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∑ s, (a * Real.sqrt (d s) - b * Real.sqrt (d' s)) ^ 2 ≤
      ∑ t, (a * Real.sqrt (d (σ t) * K t) - b * Real.sqrt (d' (σ t) * K' t)) ^ 2 := by
  have e1 : ∑ t, (a * Real.sqrt (d (σ t) * K t) - b * Real.sqrt (d' (σ t) * K' t)) ^ 2 =
      ∑ s, ∑ t, (if σ t = s then
        (a * Real.sqrt (d (σ t) * K t) - b * Real.sqrt (d' (σ t) * K' t)) ^ 2 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_ite_eq]
    simp
  rw [e1]
  apply Finset.sum_le_sum
  intro s _
  have e2 : ∑ t, (if σ t = s then
        (a * Real.sqrt (d (σ t) * K t) - b * Real.sqrt (d' (σ t) * K' t)) ^ 2 else 0) =
      ∑ t, ((a * Real.sqrt (d s)) * Real.sqrt (if σ t = s then K t else 0) -
        (b * Real.sqrt (d' s)) * Real.sqrt (if σ t = s then K' t else 0)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : σ t = s
    · simp only [h, if_true]
      rw [Real.sqrt_mul (hd s), Real.sqrt_mul (hd' s)]
      ring
    · simp [h]
  rw [e2]
  have hf : IsDist (fun t => if σ t = s then K t else 0) :=
    ⟨fun t => by dsimp only; split_ifs <;> simp [hK t], hs s⟩
  have hf' : IsDist (fun t => if σ t = s then K' t else 0) :=
    ⟨fun t => by dsimp only; split_ifs <;> simp [hK' t], hs' s⟩
  rw [sqdiff_eq _ _ hf hf']
  have h1 := aff_le_one _ _ hf hf'
  have h2 : 0 ≤ (a * Real.sqrt (d s)) * (b * Real.sqrt (d' s)) :=
    mul_nonneg (mul_nonneg ha (Real.sqrt_nonneg _)) (mul_nonneg hb (Real.sqrt_nonneg _))
  nlinarith

theorem trajLaw_init {m : ℕ} (d1 : S → ℝ) (M : TabMDP S A W (m + 1)) (π : Policy S A (m + 1))
    (τ : Traj S A W (m + 1)) :
    trajLaw d1 M π τ = d1 (τ 0).1 * trajLaw (fun _ => (1 : ℝ)) M π τ := by
  unfold trajLaw
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [Fin.succ_ne_zero]
  ring

section fin2
variable [Fintype S] [Fintype A] [Fintype W]

theorem fiber_sum [DecidableEq S] {m : ℕ} (M : TabMDP S A W (m + 1)) (π : Policy S A (m + 1))
    (hM : IsTabMDP M) (hπ : IsPolicy π) (s : S) :
    ∑ τ : Traj S A W (m + 1), (if (τ 0).1 = s then trajLaw (fun _ => (1 : ℝ)) M π τ else 0) = 1 := by
  have hd : IsDist (fun s' : S => if s' = s then (1 : ℝ) else 0) :=
    ⟨fun s' => by dsimp only; split_ifs <;> simp, by simp⟩
  have := (trajLaw_prob (m + 1) _ M π hd hM hπ).2
  have key : ∀ τ : Traj S A W (m + 1), (if (τ 0).1 = s then trajLaw (fun _ => (1 : ℝ)) M π τ else 0) =
      trajLaw (fun s' : S => if s' = s then (1 : ℝ) else 0) M π τ := by
    intro τ
    rw [trajLaw_init (fun s' : S => if s' = s then (1 : ℝ) else 0)]
    by_cases h : (τ 0).1 = s <;> simp [h]
  rw [Finset.sum_congr rfl (fun τ _ => key τ)]
  exact this

theorem trajLaw_nonneg' {n : ℕ} (d1 : S → ℝ) (M : TabMDP S A W n) (π : Policy S A n)
    (hd : ∀ s, 0 ≤ d1 s) (hM : IsTabMDP M) (hπ : IsPolicy π) (τ : Traj S A W n) :
    0 ≤ trajLaw d1 M π τ := by
  unfold trajLaw
  apply Finset.prod_nonneg
  intro h _
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  · split_ifs
    · exact hd _
    · exact zero_le_one
  · exact (hπ h _).1 _
  · exact (hM.2 h _ _).1 _
  · unfold nextWeight
    split_ifs
    · exact (hM.1 h _ _).1 _
    · exact zero_le_one

theorem trajLaw_init_nonneg {m : ℕ} (M : TabMDP S A W (m + 1)) (π : Policy S A (m + 1))
    (hM : IsTabMDP M) (hπ : IsPolicy π) (τ : Traj S A W (m + 1)) :
    0 ≤ trajLaw (fun _ => (1 : ℝ)) M π τ :=
  trajLaw_nonneg' _ M π (fun _ => zero_le_one) hM hπ τ

end fin2

section layer
variable [Fintype S] [Fintype A] [Fintype W]

theorem localHellinger_shift {n : ℕ} (M Mb : TabMDP S A W (n + 1)) (j : Fin n) (s : S) (a : A) :
    localHellinger (shiftM M) (shiftM Mb) j s a = localHellinger M Mb j.succ s a := by
  unfold localHellinger
  simp only [shiftM, Fin.val_succ]
  by_cases h : j.val + 1 < n
  · have h2 : j.val + 1 + 1 < n + 1 := by omega
    rw [if_pos h, if_pos h2]
  · have h2 : ¬ (j.val + 1 + 1 < n + 1) := by omega
    rw [if_neg h, if_neg h2]

open Classical in
theorem layer_zero_one (d1a d1b : S → ℝ) (M Mb : TabMDP S A W 1) (π : Policy S A 1)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hda : IsDist d1a) (hdb : IsDist d1b)
    (hM : IsTabMDP M) (hMb : IsTabMDP Mb) (hπ : IsPolicy π) :
    β ^ 2 / 4 * ∑ s, ∑ a, occ d1b Mb π 0 s a * localHellinger M Mb 0 s a ≤
      ∑ τ, (α * Real.sqrt (trajLaw d1a M π τ) - β * Real.sqrt (trajLaw d1b Mb π τ)) ^ 2 := by
  rw [sum_traj_succ]
  have e1 : ∀ x : S × A × W, ∑ τ' : Traj S A W 0,
      (α * Real.sqrt (trajLaw d1a M π (Fin.cons (α := fun _ => S × A × W) x τ')) -
        β * Real.sqrt (trajLaw d1b Mb π (Fin.cons (α := fun _ => S × A × W) x τ'))) ^ 2 =
      (α * Real.sqrt (d1a x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2) -
        β * Real.sqrt (d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2)) ^ 2 := by
    intro x
    simp only [trajLaw_cons]
    simp [trajLaw]
  simp_rw [e1]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [occ_zero d1b Mb π hdb hMb hπ s a]
  have hdl : localHellinger M Mb 0 s a = hellingerSq (M.R 0 s a) (Mb.R 0 s a) := by
    simp [localHellinger]
  rw [hdl]
  have h1 := one_step' (M.R 0 s a) (Mb.R 0 s a) (hM.2 0 s a) (hMb.2 0 s a)
    (α * Real.sqrt (d1a s * π 0 s a)) (β * Real.sqrt (d1b s * π 0 s a))
    (mul_nonneg hα (Real.sqrt_nonneg _)) (mul_nonneg hβ (Real.sqrt_nonneg _))
  have hpa : 0 ≤ d1a s * π 0 s a := mul_nonneg (hda.1 s) ((hπ 0 s).1 a)
  have hpb : 0 ≤ d1b s * π 0 s a := mul_nonneg (hdb.1 s) ((hπ 0 s).1 a)
  have h2 : (β * Real.sqrt (d1b s * π 0 s a)) ^ 2 = β ^ 2 * (d1b s * π 0 s a) := by
    rw [mul_pow, Real.sq_sqrt hpb]
  have h3 : ∀ w, (α * Real.sqrt (d1a s * π 0 s a * M.R 0 s a w) -
        β * Real.sqrt (d1b s * π 0 s a * Mb.R 0 s a w)) ^ 2 =
      (α * Real.sqrt (d1a s * π 0 s a) * Real.sqrt (M.R 0 s a w) -
        β * Real.sqrt (d1b s * π 0 s a) * Real.sqrt (Mb.R 0 s a w)) ^ 2 := by
    intro w
    rw [Real.sqrt_mul hpa, Real.sqrt_mul hpb]
    ring
  simp_rw [h3]
  rw [h2] at h1
  nlinarith [h1]

end layer

section layer2
variable [Fintype S] [Fintype A] [Fintype W]

open Classical in
theorem layer_zero_succ {m : ℕ} (d1a d1b : S → ℝ) (M Mb : TabMDP S A W (m + 1 + 1))
    (π : Policy S A (m + 1 + 1))
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hda : IsDist d1a) (hdb : IsDist d1b)
    (hM : IsTabMDP M) (hMb : IsTabMDP Mb) (hπ : IsPolicy π) :
    β ^ 2 / 4 * ∑ s, ∑ a, occ d1b Mb π 0 s a * localHellinger M Mb 0 s a ≤
      ∑ τ, (α * Real.sqrt (trajLaw d1a M π τ) - β * Real.sqrt (trajLaw d1b Mb π τ)) ^ 2 := by
  rw [sum_traj_succ]
  have hM' := isTab_shift hM
  have hMb' := isTab_shift hMb
  have hπ' := isPolicy_shift hπ
  have step : ∀ x : S × A × W,
      ∑ s' : S, ((α * Real.sqrt (d1a x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2)) *
          Real.sqrt (M.P 0 x.1 x.2.1 s') -
        (β * Real.sqrt (d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2)) *
          Real.sqrt (Mb.P 0 x.1 x.2.1 s')) ^ 2 ≤
      ∑ τ' : Traj S A W (m + 1),
      (α * Real.sqrt (trajLaw d1a M π (Fin.cons (α := fun _ => S × A × W) x τ')) -
        β * Real.sqrt (trajLaw d1b Mb π (Fin.cons (α := fun _ => S × A × W) x τ'))) ^ 2 := by
    intro x
    have hpa : 0 ≤ d1a x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2 :=
      mul_nonneg (mul_nonneg (hda.1 _) ((hπ 0 x.1).1 _)) ((hM.2 0 x.1 x.2.1).1 _)
    have hpb : 0 ≤ d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2 :=
      mul_nonneg (mul_nonneg (hdb.1 _) ((hπ 0 x.1).1 _)) ((hMb.2 0 x.1 x.2.1).1 _)
    have inner : ∀ τ' : Traj S A W (m + 1),
        (α * Real.sqrt (trajLaw d1a M π (Fin.cons (α := fun _ => S × A × W) x τ')) -
          β * Real.sqrt (trajLaw d1b Mb π (Fin.cons (α := fun _ => S × A × W) x τ'))) ^ 2 =
        ((α * Real.sqrt (d1a x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2)) *
            Real.sqrt (M.P 0 x.1 x.2.1 (τ' 0).1 * trajLaw (fun _ => (1 : ℝ)) (shiftM M) (shiftPi π) τ') -
          (β * Real.sqrt (d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2)) *
            Real.sqrt (Mb.P 0 x.1 x.2.1 (τ' 0).1 *
              trajLaw (fun _ => (1 : ℝ)) (shiftM Mb) (shiftPi π) τ')) ^ 2 := by
      intro τ'
      rw [trajLaw_cons, trajLaw_cons,
        trajLaw_init (fun s' => M.P 0 x.1 x.2.1 s') (shiftM M) (shiftPi π) τ',
        trajLaw_init (fun s' => Mb.P 0 x.1 x.2.1 s') (shiftM Mb) (shiftPi π) τ',
        Real.sqrt_mul hpa, Real.sqrt_mul hpb]
      ring
    simp_rw [inner]
    have hm := marg_abstract (S := S) (fun τ' : Traj S A W (m + 1) => (τ' 0).1)
      (trajLaw (fun _ => (1 : ℝ)) (shiftM M) (shiftPi π))
      (trajLaw (fun _ => (1 : ℝ)) (shiftM Mb) (shiftPi π))
      (trajLaw_init_nonneg _ _ hM' hπ') (trajLaw_init_nonneg _ _ hMb' hπ')
      (fiber_sum _ _ hM' hπ') (fiber_sum _ _ hMb' hπ')
      (fun s' => M.P 0 x.1 x.2.1 s') (fun s' => Mb.P 0 x.1 x.2.1 s')
      (fun s' => (hM.1 0 x.1 x.2.1).1 s') (fun s' => (hMb.1 0 x.1 x.2.1).1 s')
      (α * Real.sqrt (d1a x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2))
      (β * Real.sqrt (d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2))
      (mul_nonneg hα (Real.sqrt_nonneg _)) (mul_nonneg hβ (Real.sqrt_nonneg _))
    exact hm
  refine le_trans ?_ (Finset.sum_le_sum (fun x _ => step x))
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [occ_zero d1b Mb π hdb hMb hπ s a]
  have hdl : localHellinger M Mb 0 s a =
      hellingerSq (M.P 0 s a) (Mb.P 0 s a) + hellingerSq (M.R 0 s a) (Mb.R 0 s a) := by
    simp [localHellinger]
  rw [hdl]
  have h1 := one_step (M.R 0 s a) (Mb.R 0 s a) (M.P 0 s a) (Mb.P 0 s a)
    (hM.2 0 s a) (hMb.2 0 s a) (hM.1 0 s a) (hMb.1 0 s a)
    (α * Real.sqrt (d1a s * π 0 s a)) (β * Real.sqrt (d1b s * π 0 s a))
    (mul_nonneg hα (Real.sqrt_nonneg _)) (mul_nonneg hβ (Real.sqrt_nonneg _))
  have hpa : 0 ≤ d1a s * π 0 s a := mul_nonneg (hda.1 s) ((hπ 0 s).1 a)
  have hpb : 0 ≤ d1b s * π 0 s a := mul_nonneg (hdb.1 s) ((hπ 0 s).1 a)
  have h2 : (β * Real.sqrt (d1b s * π 0 s a)) ^ 2 = β ^ 2 * (d1b s * π 0 s a) := by
    rw [mul_pow, Real.sq_sqrt hpb]
  have h3 : ∀ w s', ((α * Real.sqrt (d1a s * π 0 s a * M.R 0 s a w)) * Real.sqrt (M.P 0 s a s') -
        (β * Real.sqrt (d1b s * π 0 s a * Mb.R 0 s a w)) * Real.sqrt (Mb.P 0 s a s')) ^ 2 =
      (α * Real.sqrt (d1a s * π 0 s a) * Real.sqrt (M.R 0 s a w * M.P 0 s a s') -
        β * Real.sqrt (d1b s * π 0 s a) * Real.sqrt (Mb.R 0 s a w * Mb.P 0 s a s')) ^ 2 := by
    intro w s'
    rw [Real.sqrt_mul hpa, Real.sqrt_mul hpb, Real.sqrt_mul ((hM.2 0 s a).1 w),
      Real.sqrt_mul ((hMb.2 0 s a).1 w)]
    ring
  simp_rw [h3]
  rw [h2] at h1
  nlinarith [h1]

end layer2

section layer3
variable [Fintype S] [Fintype A] [Fintype W]

open Classical in
theorem occ_succ_weighted {n : ℕ} (d1 : S → ℝ) (M Mb : TabMDP S A W (n + 1)) (π : Policy S A (n + 1))
    (j : Fin n) :
    ∑ s, ∑ a, occ d1 Mb π j.succ s a * localHellinger M Mb j.succ s a =
      ∑ x : S × A × W, d1 x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2 *
        ∑ s, ∑ a, occ (fun s' => Mb.P 0 x.1 x.2.1 s') (shiftM Mb) (shiftPi π) j s a *
          localHellinger (shiftM M) (shiftM Mb) j s a := by
  simp_rw [occ_succ, localHellinger_shift, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun s _ => Finset.sum_comm), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  ring

open Classical in
theorem layer : ∀ (n : ℕ) (d1a d1b : S → ℝ) (M Mb : TabMDP S A W n) (π : Policy S A n) (h : Fin n)
    (α β : ℝ), 0 ≤ α → 0 ≤ β → IsDist d1a → IsDist d1b → IsTabMDP M → IsTabMDP Mb → IsPolicy π →
    β ^ 2 / 4 * ∑ s, ∑ a, occ d1b Mb π h s a * localHellinger M Mb h s a ≤
      ∑ τ, (α * Real.sqrt (trajLaw d1a M π τ) - β * Real.sqrt (trajLaw d1b Mb π τ)) ^ 2 := by
  intro n
  induction n with
  | zero => intro d1a d1b M Mb π h; exact h.elim0
  | succ n ih =>
    intro d1a d1b M Mb π h α β hα hβ hda hdb hM hMb hπ
    cases h using Fin.cases with
    | zero =>
      cases n with
      | zero => exact layer_zero_one d1a d1b M Mb π α β hα hβ hda hdb hM hMb hπ
      | succ m => exact layer_zero_succ d1a d1b M Mb π α β hα hβ hda hdb hM hMb hπ
    | succ j =>
      have hM' := isTab_shift hM
      have hMb' := isTab_shift hMb
      have hπ' := isPolicy_shift hπ
      rw [occ_succ_weighted, sum_traj_succ, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      have hpa : 0 ≤ d1a x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2 :=
        mul_nonneg (mul_nonneg (hda.1 _) ((hπ 0 x.1).1 _)) ((hM.2 0 x.1 x.2.1).1 _)
      have hpb : 0 ≤ d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2 :=
        mul_nonneg (mul_nonneg (hdb.1 _) ((hπ 0 x.1).1 _)) ((hMb.2 0 x.1 x.2.1).1 _)
      have key := ih (fun s' => M.P 0 x.1 x.2.1 s') (fun s' => Mb.P 0 x.1 x.2.1 s')
        (shiftM M) (shiftM Mb) (shiftPi π) j
        (α * Real.sqrt (d1a x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2))
        (β * Real.sqrt (d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2))
        (mul_nonneg hα (Real.sqrt_nonneg _)) (mul_nonneg hβ (Real.sqrt_nonneg _))
        (hM.1 0 x.1 x.2.1) (hMb.1 0 x.1 x.2.1) hM' hMb' hπ'
      have e1 : (β * Real.sqrt (d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2)) ^ 2 =
          β ^ 2 * (d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2) := by
        rw [mul_pow, Real.sq_sqrt hpb]
      rw [e1] at key
      have e2 : ∀ τ' : Traj S A W n,
          (α * Real.sqrt (trajLaw d1a M π (Fin.cons (α := fun _ => S × A × W) x τ')) -
            β * Real.sqrt (trajLaw d1b Mb π (Fin.cons (α := fun _ => S × A × W) x τ'))) ^ 2 =
          ((α * Real.sqrt (d1a x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2)) *
              Real.sqrt (trajLaw (fun s' => M.P 0 x.1 x.2.1 s') (shiftM M) (shiftPi π) τ') -
            (β * Real.sqrt (d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2)) *
              Real.sqrt (trajLaw (fun s' => Mb.P 0 x.1 x.2.1 s') (shiftM Mb) (shiftPi π) τ')) ^ 2 := by
        intro τ'
        rw [trajLaw_cons, trajLaw_cons, Real.sqrt_mul hpa, Real.sqrt_mul hpb]
        ring
      simp_rw [e2]
      calc β ^ 2 / 4 * (d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2 *
            ∑ s, ∑ a, occ (fun s' => Mb.P 0 x.1 x.2.1 s') (shiftM Mb) (shiftPi π) j s a *
              localHellinger (shiftM M) (shiftM Mb) j s a)
          = β ^ 2 * (d1b x.1 * π 0 x.1 x.2.1 * Mb.R 0 x.1 x.2.1 x.2.2) / 4 *
            ∑ s, ∑ a, occ (fun s' => Mb.P 0 x.1 x.2.1 s') (shiftM Mb) (shiftPi π) j s a *
              localHellinger (shiftM M) (shiftM Mb) j s a := by ring
        _ ≤ _ := key

end layer3

/-! ### simulation lemma: real-analysis part -/

theorem hel_abs {Y : Type*} [Fintype Y] (P Q ψ : Y → ℝ) (hP : IsDist P) (hQ : IsDist Q)
    (h0 : ∀ y, 0 ≤ ψ y) (h1 : ∀ y, ψ y ≤ 1) :
    |∑ y, (P y - Q y) * ψ y| ≤ Real.sqrt (hellingerSq P Q) := by
  have c0 : ∑ y, (P y - Q y) * ψ y = ∑ y, (P y - Q y) * (ψ y - 1 / 2) := by
    have : ∑ y, (P y - Q y) * (ψ y - 1 / 2) = ∑ y, (P y - Q y) * ψ y - (1 / 2) * ∑ y, (P y - Q y) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _; ring
    rw [this, Finset.sum_sub_distrib, hP.2, hQ.2]
    ring
  have e : ∀ y, (P y - Q y) * (ψ y - 1 / 2) =
      (Real.sqrt (P y) - Real.sqrt (Q y)) * ((Real.sqrt (P y) + Real.sqrt (Q y)) * (ψ y - 1 / 2)) := by
    intro y
    have a1 := Real.sq_sqrt (hP.1 y)
    have a2 := Real.sq_sqrt (hQ.1 y)
    calc (P y - Q y) * (ψ y - 1 / 2)
        = (Real.sqrt (P y) ^ 2 - Real.sqrt (Q y) ^ 2) * (ψ y - 1 / 2) := by rw [a1, a2]
      _ = _ := by ring
  rw [c0]
  simp_rw [e]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun y => Real.sqrt (P y) - Real.sqrt (Q y))
    (fun y => (Real.sqrt (P y) + Real.sqrt (Q y)) * (ψ y - 1 / 2))
  have hb : ∑ y, ((Real.sqrt (P y) + Real.sqrt (Q y)) * (ψ y - 1 / 2)) ^ 2 ≤ 1 := by
    calc ∑ y, ((Real.sqrt (P y) + Real.sqrt (Q y)) * (ψ y - 1 / 2)) ^ 2
        ≤ ∑ y, ((P y + Q y + 2 * (Real.sqrt (P y) * Real.sqrt (Q y))) / 4) := by
          apply Finset.sum_le_sum
          intro y _
          have a1 := Real.sq_sqrt (hP.1 y)
          have a2 := Real.sq_sqrt (hQ.1 y)
          have hψ : (ψ y - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith [h0 y, h1 y]
          have hs : 0 ≤ (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 := sq_nonneg _
          calc ((Real.sqrt (P y) + Real.sqrt (Q y)) * (ψ y - 1 / 2)) ^ 2
              = (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 * (ψ y - 1 / 2) ^ 2 := by ring
            _ ≤ (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 * (1 / 4) := by
                exact mul_le_mul_of_nonneg_left hψ hs
            _ = _ := by nlinarith
      _ = (2 + 2 * aff P Q) / 4 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, hP.2, hQ.2,
            ← Finset.mul_sum]
          unfold aff
          ring
      _ ≤ 1 := by linarith [aff_le_one P Q hP hQ]
  have hD : 0 ≤ hellingerSq P Q := hellingerSq_nonneg' P Q
  apply Real.abs_le_sqrt
  calc _ ≤ (∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2) *
        ∑ y, ((Real.sqrt (P y) + Real.sqrt (Q y)) * (ψ y - 1 / 2)) ^ 2 := cs
    _ = hellingerSq P Q * ∑ y, ((Real.sqrt (P y) + Real.sqrt (Q y)) * (ψ y - 1 / 2)) ^ 2 := rfl
    _ ≤ hellingerSq P Q * 1 := mul_le_mul_of_nonneg_left hb hD
    _ = _ := by ring

theorem one_sim {Y Z : Type*} [Fintype Y] [Fintype Z] (f f' : Y → ℝ) (g g' : Z → ℝ)
    (hf : IsDist f) (hf' : IsDist f') (hg : IsDist g) (hg' : IsDist g')
    (r : Y → ℝ) (v : Z → ℝ) (hr0 : ∀ y, 0 ≤ r y) (hr1 : ∀ y, r y ≤ 1)
    (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    |∑ y, (f y - f' y) * r y + ∑ z, (g z - g' z) * v z| ≤
      Real.sqrt 2 * Real.sqrt (hellingerSq f f' + hellingerSq g g') := by
  have h1 := hel_abs f f' r hf hf' hr0 hr1
  have h2 := hel_abs g g' v hg hg' hv0 hv1
  have hDf := hellingerSq_nonneg' f f'
  have hDg := hellingerSq_nonneg' g g'
  have sf := Real.sq_sqrt hDf
  have sg := Real.sq_sqrt hDg
  have sf0 := Real.sqrt_nonneg (hellingerSq f f')
  have sg0 := Real.sqrt_nonneg (hellingerSq g g')
  have h3 : Real.sqrt (hellingerSq f f') + Real.sqrt (hellingerSq g g') ≤
      Real.sqrt 2 * Real.sqrt (hellingerSq f f' + hellingerSq g g') := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (Real.sqrt (hellingerSq f f') - Real.sqrt (hellingerSq g g'))]
  calc _ ≤ |∑ y, (f y - f' y) * r y| + |∑ z, (g z - g' z) * v z| := abs_add_le _ _
    _ ≤ Real.sqrt (hellingerSq f f') + Real.sqrt (hellingerSq g g') := add_le_add h1 h2
    _ ≤ _ := h3


section sim
variable [Fintype S] [Fintype A] [Fintype W]

theorem sum_aux {T : Type*} [Fintype T] (Tw R : T → ℝ) (p r : ℝ) (hT : ∑ t, Tw t = 1) :
    ∑ t, (p * Tw t) * (r + R t) = p * (r + ∑ t, Tw t * R t) := by
  have : ∀ t, (p * Tw t) * (r + R t) = p * r * Tw t + p * (Tw t * R t) := fun t => by ring
  rw [Finset.sum_congr rfl (fun t _ => this t), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hT]
  ring

theorem value_cons {n : ℕ} (rv : W → ℝ) (d1 : S → ℝ) (M : TabMDP S A W (n + 1))
    (π : Policy S A (n + 1)) (hM : IsTabMDP M) (hπ : IsPolicy π) :
    value d1 rv M π = ∑ x : S × A × W, d1 x.1 * π 0 x.1 x.2.1 * M.R 0 x.1 x.2.1 x.2.2 *
      (rv x.2.2 + value (fun s' => M.P 0 x.1 x.2.1 s') rv (shiftM M) (shiftPi π)) := by
  unfold value
  rw [sum_traj_succ]
  apply Finset.sum_congr rfl
  intro x _
  have hT := (trajLaw_prob n (fun s' => M.P 0 x.1 x.2.1 s') (shiftM M) (shiftPi π)
    (hM.1 0 x.1 x.2.1) (isTab_shift hM) (isPolicy_shift hπ)).2
  simp only [trajLaw_cons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  exact sum_aux _ _ _ _ hT

open Classical in
theorem value_linear {m : ℕ} (rv : W → ℝ) (d : S → ℝ) (M : TabMDP S A W (m + 1))
    (π : Policy S A (m + 1)) :
    value d rv M π = ∑ s, d s * value (fun s' => if s' = s then (1 : ℝ) else 0) rv M π := by
  unfold value
  have e1 : ∀ s, d s * ∑ τ : Traj S A W (m + 1),
      trajLaw (fun s' => if s' = s then (1 : ℝ) else 0) M π τ * ∑ h, rv (τ h).2.2 =
      ∑ τ : Traj S A W (m + 1), (if (τ 0).1 = s then
        d s * (trajLaw (fun _ => (1 : ℝ)) M π τ * ∑ h, rv (τ h).2.2) else 0) := by
    intro s
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    rw [trajLaw_init (fun s' : S => if s' = s then (1 : ℝ) else 0)]
    by_cases h : (τ 0).1 = s <;> simp [h]
  simp_rw [e1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  rw [trajLaw_init d]
  rw [Finset.sum_eq_single (τ 0).1]
  · simp only [if_true]; ring
  · intro b _ hb; simp [Ne.symm hb]
  · simp

def consPolicy [DecidableEq A] {n : ℕ} (a0 : A) (π' : Policy S A n) : Policy S A (n + 1) :=
  Fin.cons (α := fun _ => S → A → ℝ) (fun _ a => if a = a0 then (1 : ℝ) else 0) π'

theorem shiftPi_consPolicy [DecidableEq A] {n : ℕ} (a0 : A) (π' : Policy S A n) :
    shiftPi (consPolicy a0 π') = π' := by
  funext j
  simp [shiftPi, consPolicy]

theorem consPolicy_zero [DecidableEq A] {n : ℕ} (a0 : A) (π' : Policy S A n) (s : S) (a : A) :
    consPolicy a0 π' 0 s a = if a = a0 then (1 : ℝ) else 0 := by
  simp [consPolicy]

theorem isPolicy_cons [DecidableEq A] {n : ℕ} (a0 : A) {π' : Policy S A n} (h : IsPolicy π') :
    IsPolicy (consPolicy a0 π') := by
  intro j s
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [show consPolicy a0 π' 0 s = fun a => if a = a0 then (1 : ℝ) else 0 from
      funext (fun a => consPolicy_zero a0 π' s a)]
    exact ⟨fun a => by dsimp only; split_ifs <;> simp, by simp⟩
  · have : consPolicy a0 π' i.succ s = π' i s := by simp [consPolicy]
    rw [this]
    exact h i s

noncomputable def suffixWeight {H : ℕ} (M : TabMDP S A W H) (π : Policy S A H) (k : Fin H)
    (τ : Traj S A W H) : ℝ :=
  ∏ h ∈ (Finset.univ.filter (fun h : Fin H => k.val ≤ h.val)),
    π h (τ h).1 (τ h).2.1 * M.R h (τ h).1 (τ h).2.1 (τ h).2.2 * nextWeight M τ h

/-- the suffix clause -/
def Suf {n : ℕ} (rv : W → ℝ) (M : TabMDP S A W n) : Prop :=
  ∀ (π : Policy S A n) (k : Fin n) (τ : Traj S A W n), IsPolicy π →
    suffixWeight M π k τ ≠ 0 →
    ∑ h ∈ (Finset.univ.filter (fun h : Fin n => k.val ≤ h.val)), rv (τ h).2.2 ≤ 1

end sim

section sim3
variable [Fintype S] [Fintype A] [Fintype W]

open Classical in
theorem suf_shift [Nonempty S] [Nonempty A] [Nonempty W] {n : ℕ} (rv : W → ℝ)
    (M : TabMDP S A W (n + 1)) (h : Suf rv M) : Suf rv (shiftM M) := by
  intro π' k τ' hπ' hne
  have hπ := isPolicy_cons (S := S) (Classical.arbitrary A) hπ'
  let x0 : S × A × W := (Classical.arbitrary S, Classical.arbitrary A, Classical.arbitrary W)
  have hsw : suffixWeight M (consPolicy (S := S) (Classical.arbitrary A) π') k.succ
      (Fin.cons (α := fun _ => S × A × W) x0 τ' : Traj S A W (n + 1)) =
      suffixWeight (shiftM M) π' k τ' := by
    unfold suffixWeight
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
    have h0 : ¬ (k.succ.val ≤ (0 : Fin (n + 1)).val) := by simp
    rw [if_neg h0, one_mul]
    apply Finset.prod_congr rfl
    intro j _
    have hj : (k.succ.val ≤ j.succ.val) ↔ (k.val ≤ j.val) := by simp
    by_cases hkj : k.val ≤ j.val
    · rw [if_pos (hj.2 hkj), if_pos hkj]
      simp only [consPolicy, Fin.cons_succ, nextWeight_cons_succ, shiftM]
    · rw [if_neg (fun h' => hkj (hj.1 h')), if_neg hkj]
  have hsum : ∑ i ∈ (Finset.univ.filter (fun i : Fin (n + 1) => k.succ.val ≤ i.val)),
      rv ((Fin.cons (α := fun _ => S × A × W) x0 τ' : Traj S A W (n + 1)) i).2.2 =
      ∑ j ∈ (Finset.univ.filter (fun j : Fin n => k.val ≤ j.val)), rv (τ' j).2.2 := by
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
    have h0 : ¬ (k.succ.val ≤ (0 : Fin (n + 1)).val) := by simp
    rw [if_neg h0, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    have hj : (k.succ.val ≤ j.succ.val) ↔ (k.val ≤ j.val) := by simp
    by_cases hkj : k.val ≤ j.val
    · rw [if_pos (hj.2 hkj), if_pos hkj]
      simp
    · rw [if_neg (fun h' => hkj (hj.1 h')), if_neg hkj]
  have := h (consPolicy (S := S) (Classical.arbitrary A) π') k.succ
    (Fin.cons (α := fun _ => S × A × W) x0 τ') hπ (by rw [hsw]; exact hne)
  rw [hsum] at this
  exact this

theorem trajLaw_one_suffix {m : ℕ} (M : TabMDP S A W (m + 1)) (π : Policy S A (m + 1))
    (τ : Traj S A W (m + 1)) :
    trajLaw (fun _ => (1 : ℝ)) M π τ = suffixWeight M π ⟨0, Nat.succ_pos m⟩ τ := by
  unfold trajLaw suffixWeight
  rw [Finset.filter_true_of_mem (fun h _ => Nat.zero_le _)]
  apply Finset.prod_congr rfl
  intro h _
  simp

open Classical in
theorem value_dirac_bounds {n : ℕ} (rv : W → ℝ) (hrv : ∀ w, 0 ≤ rv w ∧ rv w ≤ 1)
    (M : TabMDP S A W n) (π : Policy S A n) (hM : IsTabMDP M) (hπ : IsPolicy π)
    (hS : Suf rv M) (s : S) :
    0 ≤ value (fun s' => if s' = s then (1 : ℝ) else 0) rv M π ∧
      value (fun s' => if s' = s then (1 : ℝ) else 0) rv M π ≤ 1 := by
  cases n with
  | zero => simp [value]
  | succ m =>
    have hd : IsDist (fun s' : S => if s' = s then (1 : ℝ) else 0) :=
      ⟨fun s' => by dsimp only; split_ifs <;> simp, by simp⟩
    have hp := trajLaw_prob (m + 1) _ M π hd hM hπ
    unfold value
    constructor
    · apply Finset.sum_nonneg
      intro τ _
      exact mul_nonneg (hp.1 τ) (Finset.sum_nonneg (fun h _ => (hrv _).1))
    · calc _ ≤ ∑ τ, trajLaw (fun s' : S => if s' = s then (1 : ℝ) else 0) M π τ := by
            apply Finset.sum_le_sum
            intro τ _
            by_cases hz : trajLaw (fun s' : S => if s' = s then (1 : ℝ) else 0) M π τ = 0
            · rw [hz]; simp
            · have hne : suffixWeight M π ⟨0, Nat.succ_pos m⟩ τ ≠ 0 := by
                intro h0
                apply hz
                rw [trajLaw_init, trajLaw_one_suffix, h0, mul_zero]
              have := hS π ⟨0, Nat.succ_pos m⟩ τ hπ hne
              rw [Finset.filter_true_of_mem (fun h _ => Nat.zero_le _)] at this
              calc _ ≤ trajLaw (fun s' : S => if s' = s then (1 : ℝ) else 0) M π τ * 1 :=
                    mul_le_mul_of_nonneg_left this (hp.1 τ)
                _ = _ := mul_one _
        _ = 1 := hp.2

end sim3

section sim4
variable [Fintype S] [Fintype A] [Fintype W]

theorem value_cons' {n : ℕ} (rv : W → ℝ) (d1 : S → ℝ) (M : TabMDP S A W (n + 1))
    (π : Policy S A (n + 1)) (hM : IsTabMDP M) (hπ : IsPolicy π) :
    value d1 rv M π = ∑ s, ∑ a, d1 s * π 0 s a *
      (∑ w, M.R 0 s a w * rv w + value (fun s' => M.P 0 s a s') rv (shiftM M) (shiftPi π)) := by
  rw [value_cons rv d1 M π hM hπ, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  have h1 : ∀ w, d1 s * π 0 s a * M.R 0 s a w * (rv w + value (fun s' => M.P 0 s a s') rv (shiftM M) (shiftPi π)) =
      d1 s * π 0 s a * (M.R 0 s a w * rv w) +
        d1 s * π 0 s a * value (fun s' => M.P 0 s a s') rv (shiftM M) (shiftPi π) * M.R 0 s a w := by
    intro w; ring
  simp only [h1]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hM.2 0 s a).2]
  ring

open Classical in
theorem occ_succ' {n : ℕ} (d1 : S → ℝ) (Mb : TabMDP S A W (n + 1)) (π : Policy S A (n + 1))
    (hMb : IsTabMDP Mb) (j : Fin n) (s : S) (a : A) :
    occ d1 Mb π j.succ s a = ∑ s0, ∑ a0, d1 s0 * π 0 s0 a0 *
      occ (fun s' => Mb.P 0 s0 a0 s') (shiftM Mb) (shiftPi π) j s a := by
  rw [occ_succ, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s0 _
  apply Finset.sum_congr rfl
  intro a0 _
  have h1 : ∀ w, d1 s0 * π 0 s0 a0 * Mb.R 0 s0 a0 w *
      occ (fun s' => Mb.P 0 s0 a0 s') (shiftM Mb) (shiftPi π) j s a =
      d1 s0 * π 0 s0 a0 * occ (fun s' => Mb.P 0 s0 a0 s') (shiftM Mb) (shiftPi π) j s a *
        Mb.R 0 s0 a0 w := by
    intro w; ring
  simp only [h1]
  rw [← Finset.mul_sum, (hMb.2 0 s0 a0).2]
  ring

open Classical in
theorem layer_diff [Nonempty S] [Nonempty A] [Nonempty W] {n : ℕ} (rv : W → ℝ)
    (hrv : ∀ w, 0 ≤ rv w ∧ rv w ≤ 1)
    (M Mb : TabMDP S A W (n + 1)) (π : Policy S A (n + 1))
    (hM : IsTabMDP M) (hMb : IsTabMDP Mb) (hπ : IsPolicy π) (hS : Suf rv M) (s : S) (a : A) :
    |(∑ w, M.R 0 s a w * rv w + value (fun s' => M.P 0 s a s') rv (shiftM M) (shiftPi π)) -
      (∑ w, Mb.R 0 s a w * rv w + value (fun s' => Mb.P 0 s a s') rv (shiftM Mb) (shiftPi π))| ≤
    Real.sqrt 2 * Real.sqrt (localHellinger M Mb 0 s a) +
      |value (fun s' => Mb.P 0 s a s') rv (shiftM M) (shiftPi π) -
        value (fun s' => Mb.P 0 s a s') rv (shiftM Mb) (shiftPi π)| := by
  have hR : ∑ w, M.R 0 s a w * rv w - ∑ w, Mb.R 0 s a w * rv w =
      ∑ w, (M.R 0 s a w - Mb.R 0 s a w) * rv w := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _; ring
  cases n with
  | zero =>
    have h0 : ∀ (M' : TabMDP S A W 0) (d : S → ℝ) (π' : Policy S A 0),
        value d rv M' π' = 0 := by
      intro M' d π'; simp [value]
    simp only [h0, add_zero, sub_zero, abs_zero]
    have hdl : localHellinger M Mb 0 s a = hellingerSq (M.R 0 s a) (Mb.R 0 s a) := by
      simp [localHellinger]
    rw [hdl, hR]
    have := hel_abs (M.R 0 s a) (Mb.R 0 s a) rv (hM.2 0 s a) (hMb.2 0 s a)
      (fun w => (hrv w).1) (fun w => (hrv w).2)
    have hs2 : 1 ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs0 := Real.sqrt_nonneg (hellingerSq (M.R 0 s a) (Mb.R 0 s a))
    nlinarith
  | succ m =>
    have hM' := isTab_shift hM
    have hπ' := isPolicy_shift hπ
    have hS' := suf_shift rv M hS
    have hlin := fun (N : TabMDP S A W (m + 1)) (d : S → ℝ) =>
      value_linear rv d N (shiftPi π)
    have hv := fun s' => value_dirac_bounds rv hrv (shiftM M) (shiftPi π) hM' hπ' hS' s'
    have h1 : value (fun s' => M.P 0 s a s') rv (shiftM M) (shiftPi π) -
        value (fun s' => Mb.P 0 s a s') rv (shiftM M) (shiftPi π) =
        ∑ s', (M.P 0 s a s' - Mb.P 0 s a s') *
          value (fun s'' => if s'' = s' then (1 : ℝ) else 0) rv (shiftM M) (shiftPi π) := by
      rw [hlin (shiftM M) (fun s' => M.P 0 s a s'), hlin (shiftM M) (fun s' => Mb.P 0 s a s'),
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s' _; ring
    have hdl : localHellinger M Mb 0 s a =
        hellingerSq (M.P 0 s a) (Mb.P 0 s a) + hellingerSq (M.R 0 s a) (Mb.R 0 s a) := by
      simp [localHellinger]
    have h2 := one_sim (M.R 0 s a) (Mb.R 0 s a) (M.P 0 s a) (Mb.P 0 s a)
      (hM.2 0 s a) (hMb.2 0 s a) (hM.1 0 s a) (hMb.1 0 s a) rv
      (fun s' => value (fun s'' => if s'' = s' then (1 : ℝ) else 0) rv (shiftM M) (shiftPi π))
      (fun w => (hrv w).1) (fun w => (hrv w).2) (fun s' => (hv s').1) (fun s' => (hv s').2)
    rw [← h1, ← hR] at h2
    rw [hdl, add_comm (hellingerSq (M.P 0 s a) _)]
    have h3 : (∑ w, M.R 0 s a w * rv w + value (fun s' => M.P 0 s a s') rv (shiftM M) (shiftPi π)) -
        (∑ w, Mb.R 0 s a w * rv w + value (fun s' => Mb.P 0 s a s') rv (shiftM Mb) (shiftPi π)) =
        ((∑ w, M.R 0 s a w * rv w - ∑ w, Mb.R 0 s a w * rv w) +
          (value (fun s' => M.P 0 s a s') rv (shiftM M) (shiftPi π) -
            value (fun s' => Mb.P 0 s a s') rv (shiftM M) (shiftPi π))) +
        (value (fun s' => Mb.P 0 s a s') rv (shiftM M) (shiftPi π) -
          value (fun s' => Mb.P 0 s a s') rv (shiftM Mb) (shiftPi π)) := by ring
    rw [h3]
    calc _ ≤ |(∑ w, M.R 0 s a w * rv w - ∑ w, Mb.R 0 s a w * rv w) +
          (value (fun s' => M.P 0 s a s') rv (shiftM M) (shiftPi π) -
            value (fun s' => Mb.P 0 s a s') rv (shiftM M) (shiftPi π))| +
        |value (fun s' => Mb.P 0 s a s') rv (shiftM M) (shiftPi π) -
          value (fun s' => Mb.P 0 s a s') rv (shiftM Mb) (shiftPi π)| := abs_add_le _ _
      _ ≤ _ := by linarith [h2]

end sim4

theorem regroup {ι1 ι2 ι3 ι4 ι5 : Type*} [Fintype ι1] [Fintype ι2] [Fintype ι3] [Fintype ι4]
    [Fintype ι5] (F : ι1 → ι2 → ι3 → ι4 → ι5 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e = ∑ c, ∑ d, ∑ e, ∑ a, ∑ b, F a b c d e := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e
      = ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, F a b c d e :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, ∑ d, ∑ e, F a b c d e := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, ∑ e, F a b c d e :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
    _ = ∑ c, ∑ d, ∑ a, ∑ b, ∑ e, F a b c d e :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
    _ = ∑ c, ∑ d, ∑ a, ∑ e, ∑ b, F a b c d e :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ =>
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)))
    _ = ∑ c, ∑ d, ∑ e, ∑ a, ∑ b, F a b c d e :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => Finset.sum_comm))

section sim5
variable [Fintype S] [Fintype A] [Fintype W]

open Classical in
theorem sim [Nonempty S] [Nonempty A] [Nonempty W] (rv : W → ℝ) (hrv : ∀ w, 0 ≤ rv w ∧ rv w ≤ 1) :
    ∀ (n : ℕ) (d1 : S → ℝ) (M Mb : TabMDP S A W n) (π : Policy S A n),
    IsDist d1 → IsTabMDP M → IsTabMDP Mb → IsPolicy π → Suf rv M →
    |value d1 rv M π - value d1 rv Mb π| ≤
      Real.sqrt 2 * ∑ h : Fin n, ∑ s, ∑ a,
        occ d1 Mb π h s a * Real.sqrt (localHellinger M Mb h s a) := by
  intro n
  induction n with
  | zero => intro d1 M Mb π _ _ _ _ _; simp [value]
  | succ n ih =>
    intro d1 M Mb π hd hM hMb hπ hS
    have hM' := isTab_shift hM
    have hMb' := isTab_shift hMb
    have hπ' := isPolicy_shift hπ
    have hS' := suf_shift rv M hS
    have hih : ∀ s a, |value (fun s' => Mb.P 0 s a s') rv (shiftM M) (shiftPi π) -
        value (fun s' => Mb.P 0 s a s') rv (shiftM Mb) (shiftPi π)| ≤
        Real.sqrt 2 * ∑ j : Fin n, ∑ s2, ∑ a2,
          occ (fun s' => Mb.P 0 s a s') (shiftM Mb) (shiftPi π) j s2 a2 *
            Real.sqrt (localHellinger (shiftM M) (shiftM Mb) j s2 a2) :=
      fun s a => ih _ (shiftM M) (shiftM Mb) (shiftPi π) (hMb.1 0 s a) hM' hMb' hπ' hS'
    have hc : ∀ s a, 0 ≤ d1 s * π 0 s a := fun s a => mul_nonneg (hd.1 s) ((hπ 0 s).1 a)
    have hbound : ∀ s a, |(∑ w, M.R 0 s a w * rv w +
          value (fun s' => M.P 0 s a s') rv (shiftM M) (shiftPi π)) -
        (∑ w, Mb.R 0 s a w * rv w +
          value (fun s' => Mb.P 0 s a s') rv (shiftM Mb) (shiftPi π))| ≤
        Real.sqrt 2 * Real.sqrt (localHellinger M Mb 0 s a) +
          Real.sqrt 2 * ∑ j : Fin n, ∑ s2, ∑ a2,
            occ (fun s' => Mb.P 0 s a s') (shiftM Mb) (shiftPi π) j s2 a2 *
              Real.sqrt (localHellinger (shiftM M) (shiftM Mb) j s2 a2) := by
      intro s a
      exact le_trans (layer_diff rv hrv M Mb π hM hMb hπ hS s a) (add_le_add_right (hih s a) _)
    rw [value_cons' rv d1 M π hM hπ, value_cons' rv d1 Mb π hMb hπ, Fin.sum_univ_succ,
      ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
    calc _ ≤ ∑ s, |∑ a, d1 s * π 0 s a * _| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, ∑ a, d1 s * π 0 s a *
          (Real.sqrt 2 * Real.sqrt (localHellinger M Mb 0 s a) +
            Real.sqrt 2 * ∑ j : Fin n, ∑ s2, ∑ a2,
              occ (fun s' => Mb.P 0 s a s') (shiftM Mb) (shiftPi π) j s2 a2 *
                Real.sqrt (localHellinger (shiftM M) (shiftM Mb) j s2 a2)) := by
          apply Finset.sum_le_sum
          intro s _
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          apply Finset.sum_le_sum
          intro a _
          rw [abs_mul, abs_of_nonneg (hc s a)]
          exact mul_le_mul_of_nonneg_left (hbound s a) (hc s a)
      _ = _ := by
          have e1 : ∑ s, ∑ a, d1 s * π 0 s a * (Real.sqrt 2 * Real.sqrt (localHellinger M Mb 0 s a)) =
              Real.sqrt 2 * ∑ s, ∑ a, occ d1 Mb π 0 s a *
                Real.sqrt (localHellinger M Mb 0 s a) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            rw [occ_zero d1 Mb π hd hMb hπ s a]
            ring
          have e2 : ∑ s, ∑ a, d1 s * π 0 s a * (Real.sqrt 2 * ∑ j : Fin n, ∑ s2, ∑ a2,
                occ (fun s' => Mb.P 0 s a s') (shiftM Mb) (shiftPi π) j s2 a2 *
                  Real.sqrt (localHellinger (shiftM M) (shiftM Mb) j s2 a2)) =
              Real.sqrt 2 * ∑ j : Fin n, ∑ s2, ∑ a2,
                occ d1 Mb π j.succ s2 a2 * Real.sqrt (localHellinger M Mb j.succ s2 a2) := by
            simp_rw [occ_succ' d1 Mb π hMb, localHellinger_shift]
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [regroup]
            refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ =>
              Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ =>
                Finset.sum_congr rfl (fun _ _ => by ring)))))
          simp_rw [mul_add]
          rw [Finset.sum_congr rfl (fun s _ => Finset.sum_add_distrib), Finset.sum_add_distrib, e1, e2]

end sim5

/-! ### assembly: pure real algebra -/

/-! ### the reachability-wiped model -/

section wipe

/-- graph reachability of a state at a layer -/
inductive Reach {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H) : ℕ → S → Prop
  | init (s : S) : 0 < d1 s → Reach d1 M 0 s
  | step (h : Fin H) (s : S) (a : A) (s' : S) :
      Reach d1 M h.val s → 0 < M.P h s a s' → Reach d1 M (h.val + 1) s'

open Classical in
/-- `M` with the reward kernel at unreachable states replaced by a point mass at `w0` -/
noncomputable def wipe {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H) (w0 : W) : TabMDP S A W H where
  P := M.P
  R := fun h s a w => if Reach d1 M h.val s then M.R h s a w else if w = w0 then 1 else 0

variable [Fintype S] [Fintype A] [Fintype W]

theorem wipe_R_reach {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H) (w0 : W) (h : Fin H) (s : S)
    (hr : Reach d1 M h.val s) (a : A) (w : W) : (wipe d1 M w0).R h s a w = M.R h s a w := by
  simp [wipe, hr]

open Classical in
theorem wipe_R_unreach {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H) (w0 : W) (h : Fin H) (s : S)
    (hr : ¬ Reach d1 M h.val s) (a : A) (w : W) :
    (wipe d1 M w0).R h s a w = if w = w0 then 1 else 0 := by
  simp [wipe, hr]

theorem wipe_isTab {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H) (w0 : W) (hM : IsTabMDP M) :
    IsTabMDP (wipe d1 M w0) := by
  classical
  refine ⟨hM.1, fun h s a => ?_⟩
  by_cases hr : Reach d1 M h.val s
  · have e : (wipe d1 M w0).R h s a = M.R h s a := funext (fun w => wipe_R_reach d1 M w0 h s hr a w)
    rw [e]; exact hM.2 h s a
  · have e : (wipe d1 M w0).R h s a = fun w => if w = w0 then (1 : ℝ) else 0 :=
      funext (fun w => wipe_R_unreach d1 M w0 h s hr a w)
    rw [e]
    exact ⟨fun a => by dsimp only; split_ifs <;> simp, by simp⟩

theorem wipe_nextWeight {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H) (w0 : W) (τ : Traj S A W H)
    (h : Fin H) : nextWeight (wipe d1 M w0) τ h = nextWeight M τ h := by
  simp [nextWeight, wipe]

theorem wipe_trajLaw {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H) (w0 : W) (hd : IsDist d1)
    (hM : IsTabMDP M) (π : Policy S A H) (τ : Traj S A W H) :
    trajLaw d1 (wipe d1 M w0) π τ = trajLaw d1 M π τ := by
  classical
  by_cases hall : ∀ x : Fin H, Reach d1 M x.val (τ x).1
  · unfold trajLaw
    apply Finset.prod_congr rfl
    intro x _
    rw [wipe_R_reach d1 M w0 x (τ x).1 (hall x), wipe_nextWeight]
  · push_neg at hall
    have key : ∃ y : Fin H, (y.val = 0 ∧ d1 (τ y).1 = 0) ∨ nextWeight M τ y = 0 := by
      have hex : ∃ n, ∃ hn : n < H, ¬ Reach d1 M n (τ ⟨n, hn⟩).1 := by
        obtain ⟨x, hx⟩ := hall
        exact ⟨x.val, x.2, hx⟩
      have hfind : ∃ n0, ∃ hn0 : n0 < H, ¬ Reach d1 M n0 (τ ⟨n0, hn0⟩).1 ∧
          ∀ m (hm : m < H), m < n0 → Reach d1 M m (τ ⟨m, hm⟩).1 := by
        obtain ⟨hn0, hnr⟩ := Nat.find_spec hex
        refine ⟨Nat.find hex, hn0, hnr, fun m hm hlt => ?_⟩
        have := Nat.find_min hex hlt
        by_contra hc
        exact this ⟨hm, hc⟩
      obtain ⟨n0, hn0, hnr, hmin⟩ := hfind
      by_cases hz : n0 = 0
      · subst hz
        refine ⟨⟨0, hn0⟩, Or.inl ⟨rfl, ?_⟩⟩
        have hnr' : ¬ 0 < d1 (τ ⟨0, hn0⟩).1 := fun hp => hnr (Reach.init _ hp)
        exact le_antisymm (not_lt.mp hnr') (hd.1 _)
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hz
        subst hm
        have hmH : m < H := by omega
        have hprev : Reach d1 M m (τ ⟨m, hmH⟩).1 := hmin m hmH (by omega)
        refine ⟨⟨m, hmH⟩, Or.inr ?_⟩
        by_contra hne
        have hn' : m + 1 < H := hn0
        have hPpos : 0 < M.P ⟨m, hmH⟩ (τ ⟨m, hmH⟩).1 (τ ⟨m, hmH⟩).2.1 (τ ⟨m + 1, hn'⟩).1 := by
          have h1 : nextWeight M τ ⟨m, hmH⟩ =
              M.P ⟨m, hmH⟩ (τ ⟨m, hmH⟩).1 (τ ⟨m, hmH⟩).2.1 (τ ⟨m + 1, hn'⟩).1 := by
            simp [nextWeight, hn']
          rw [h1] at hne
          exact lt_of_le_of_ne ((hM.1 _ _ _).1 _) (Ne.symm hne)
        have := Reach.step ⟨m, hmH⟩ _ _ _ hprev hPpos
        exact hnr this
    obtain ⟨y, hy⟩ := key
    have z1 : trajLaw d1 M π τ = 0 := by
      unfold trajLaw
      apply Finset.prod_eq_zero (Finset.mem_univ y)
      rcases hy with ⟨h1, h2⟩ | h1
      · simp [h1, h2]
      · simp [h1]
    have z2 : trajLaw d1 (wipe d1 M w0) π τ = 0 := by
      unfold trajLaw
      apply Finset.prod_eq_zero (Finset.mem_univ y)
      rcases hy with ⟨h1, h2⟩ | h1
      · simp [h1, h2]
      · simp [wipe_nextWeight, h1]
    rw [z1, z2]

end wipe

section glue
variable [Fintype S] [Fintype A] [Fintype W]

def fac {H : ℕ} (M : TabMDP S A W H) (π : Policy S A H) (τ : Traj S A W H) (h : Fin H) : ℝ :=
  π h (τ h).1 (τ h).2.1 * M.R h (τ h).1 (τ h).2.1 (τ h).2.2 * nextWeight M τ h

theorem filter_split {H : ℕ} (j : ℕ) (hj : j < H) (f : Fin H → ℝ) :
    ∑ h ∈ Finset.univ.filter (fun h : Fin H => j ≤ h.val), f h =
      f ⟨j, hj⟩ + ∑ h ∈ Finset.univ.filter (fun h : Fin H => j + 1 ≤ h.val), f h := by
  have : Finset.univ.filter (fun h : Fin H => j ≤ h.val) =
      insert (⟨j, hj⟩ : Fin H) (Finset.univ.filter (fun h : Fin H => j + 1 ≤ h.val)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp)]

theorem exists_pos_R {H : ℕ} (M : TabMDP S A W H) (hM : IsTabMDP M) (h : Fin H) (s : S) (a : A) :
    ∃ w, 0 < M.R h s a w := by
  by_contra hne
  push_neg at hne
  have : ∑ w, M.R h s a w = 0 :=
    Finset.sum_eq_zero (fun w _ => le_antisymm (hne w) ((hM.2 h s a).1 w))
  have h1 := (hM.2 h s a).2
  rw [this] at h1
  exact zero_ne_one h1

theorem glue [Nonempty A] {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H) (rv : W → ℝ) (μ : ℝ)
    (hμ : ∀ w, μ ≤ rv w) (hM : IsTabMDP M) :
    ∀ (n : ℕ) (s : S), Reach d1 M n s → ∀ (hn : n < H) (τ : Traj S A W H) (π : Policy S A H),
      IsPolicy π → (τ ⟨n, hn⟩).1 = s → (∀ h : Fin H, n ≤ h.val → fac M π τ h ≠ 0) →
      ∃ (π'' : Policy S A H) (τ'' : Traj S A W H), IsPolicy π'' ∧ trajLaw d1 M π'' τ'' ≠ 0 ∧
        (n : ℝ) * μ + ∑ h ∈ Finset.univ.filter (fun h : Fin H => n ≤ h.val), rv (τ h).2.2 ≤
          ∑ h : Fin H, rv (τ'' h).2.2 := by
  classical
  intro n s hr
  induction hr with
  | init s0 hpos =>
    intro hn τ π hπ hs hgood
    refine ⟨π, τ, hπ, ?_, ?_⟩
    · unfold trajLaw
      rw [Finset.prod_ne_zero_iff]
      intro h _
      have hf := hgood h (Nat.zero_le _)
      unfold fac at hf
      obtain ⟨h12, h3⟩ := mul_ne_zero_iff.mp hf
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h12
      by_cases h0 : h.val = 0
      · have e : h = ⟨0, hn⟩ := Fin.ext h0
        have hs1 : (τ h).1 = s0 := by rw [e]; exact hs
        have hd0 : d1 (τ h).1 ≠ 0 := by rw [hs1]; exact hpos.ne'
        rw [if_pos h0]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero hd0 h1) h2) h3
      · rw [if_neg h0, one_mul]
        exact hf
    · simp
  | step h0 s0 a s' hreach hP ih =>
    intro hn τ π hπ hs hgood
    obtain ⟨w, hw⟩ := exists_pos_R M hM h0 s0 a
    set τ' : Traj S A W H := Function.update τ h0 (s0, a, w) with hτ'
    set π' : Policy S A H := fun x t b => if x = h0 ∧ t = s0 then (if b = a then 1 else 0) else π x t b
      with hπ'def
    have hπ' : IsPolicy π' := by
      intro x t
      by_cases hc : x = h0 ∧ t = s0
      · have e : π' x t = fun b => if b = a then (1 : ℝ) else 0 := by
          funext b; simp [hπ'def, hc]
        rw [e]
        exact ⟨fun b => by dsimp only; split_ifs <;> simp, by simp⟩
      · have e : π' x t = π x t := by
          funext b; simp [hπ'def, hc]
        rw [e]; exact hπ x t
    have hn0 : h0.val + 1 < H := hn
    have hτ'h0 : τ' h0 = (s0, a, w) := by simp [hτ']
    have hτ'ne : ∀ x : Fin H, x ≠ h0 → τ' x = τ x := fun x hx => by simp [hτ', hx]
    have hnext : (τ ⟨h0.val + 1, hn0⟩).1 = s' := hs
    have hgood' : ∀ x : Fin H, h0.val ≤ x.val → fac M π' τ' x ≠ 0 := by
      intro x hx
      by_cases hxe : x = h0
      · subst hxe
        unfold fac
        rw [hτ'h0]
        have e1 : π' x s0 a = 1 := by simp [hπ'def]
        have e2 : nextWeight M τ' x = M.P x s0 a s' := by
          have : (τ' ⟨x.val + 1, hn0⟩) = τ ⟨x.val + 1, hn0⟩ :=
            hτ'ne _ (by intro hh; have := congrArg Fin.val hh; simp at this)
          simp [nextWeight, hn0, this, hnext, hτ'h0]
        simp only [e1, e2]
        exact mul_ne_zero (mul_ne_zero one_ne_zero hw.ne') hP.ne'
      · have hlt : h0.val + 1 ≤ x.val := by
          have : h0.val ≠ x.val := fun hh => hxe (Fin.ext hh.symm)
          omega
        have hg := hgood x hlt
        unfold fac at hg ⊢
        have e1 : π' x (τ' x).1 (τ' x).2.1 = π x (τ x).1 (τ x).2.1 := by
          rw [hτ'ne x hxe]; simp [hπ'def, hxe]
        have e2 : nextWeight M τ' x = nextWeight M τ x := by
          unfold nextWeight
          split_ifs with hh
          · have : (τ' ⟨x.val + 1, hh⟩) = τ ⟨x.val + 1, hh⟩ :=
              hτ'ne _ (by intro h5; have := congrArg Fin.val h5; simp at this; omega)
            rw [hτ'ne x hxe, this]
          · rfl
        rw [e1, e2, hτ'ne x hxe]
        exact hg
    obtain ⟨π'', τ'', hπ'', hne, hsum⟩ := ih h0.2 τ' π' hπ' (by simp [hτ']) hgood'
    refine ⟨π'', τ'', hπ'', hne, ?_⟩
    have hs1 := filter_split h0.val h0.2 (fun h => rv (τ' h).2.2)
    have hs2 : ∑ h ∈ Finset.univ.filter (fun h : Fin H => h0.val + 1 ≤ h.val), rv (τ' h).2.2 =
        ∑ h ∈ Finset.univ.filter (fun h : Fin H => h0.val + 1 ≤ h.val), rv (τ h).2.2 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hτ'ne x (by intro hh; subst hh; omega)]
    have e0 : (⟨h0.val, h0.2⟩ : Fin H) = h0 := Fin.eta h0 h0.2
    simp only [e0, hτ'h0] at hs1
    rw [hs2] at hs1
    have := hμ w
    push_cast at hsum ⊢
    nlinarith

end glue

section wsuf
variable [Fintype S] [Fintype A] [Fintype W]

theorem wipe_suf [Nonempty A] {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H) (rv : W → ℝ)
    (hrv : ∀ w, 0 ≤ rv w ∧ rv w ≤ 1) (hd : IsDist d1) (hM : IsTabMDP M)
    (hN : ∀ π τ, IsPolicy π → trajLaw d1 M π τ ≠ 0 →
      0 ≤ ∑ h : Fin H, rv (τ h).2.2 ∧ ∑ h : Fin H, rv (τ h).2.2 ≤ 1)
    (w0 : W) (hw0 : ∀ w, rv w0 ≤ rv w) : Suf rv (wipe d1 M w0) := by
  classical
  have hμ0 : 0 ≤ rv w0 := (hrv w0).1
  have hHμ : (H : ℝ) * rv w0 ≤ 1 := by
    let a0 : A := Classical.arbitrary A
    let π0 : Policy S A H := fun _ _ b => if b = a0 then 1 else 0
    have hπ0 : IsPolicy π0 := fun h s =>
      ⟨fun b => by dsimp only [π0]; split_ifs <;> simp, by simp [π0]⟩
    have hsum := (trajLaw_prob H d1 M π0 hd hM hπ0).2
    obtain ⟨τ, _, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (show ∑ τ, trajLaw d1 M π0 τ ≠ 0 by rw [hsum]; exact one_ne_zero)
    have := (hN π0 τ hπ0 hτ).2
    calc (H : ℝ) * rv w0 = ∑ _h : Fin H, rv w0 := by simp
      _ ≤ ∑ h : Fin H, rv (τ h).2.2 := Finset.sum_le_sum (fun h _ => hw0 _)
      _ ≤ 1 := this
  intro π k τ hπ hne
  have hgood : ∀ h : Fin H, k.val ≤ h.val → fac (wipe d1 M w0) π τ h ≠ 0 := by
    intro h hh
    exact (Finset.prod_ne_zero_iff.mp hne) h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
  have claim : ∀ d : ℕ, ∀ j : ℕ, j + d = H →
      (∀ h : Fin H, j ≤ h.val → fac (wipe d1 M w0) π τ h ≠ 0) →
      ∑ h ∈ Finset.univ.filter (fun h : Fin H => j ≤ h.val), rv (τ h).2.2 ≤ 1 - (j : ℝ) * rv w0 := by
    intro d
    induction d with
    | zero =>
      intro j hj _
      have e : ∑ h ∈ Finset.univ.filter (fun h : Fin H => j ≤ h.val), rv (τ h).2.2 = 0 := by
        apply Finset.sum_eq_zero
        intro h hh
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
        have := h.2
        omega
      rw [e]
      have : (j : ℝ) = H := by exact_mod_cast (by omega : j = H)
      rw [this]; linarith
    | succ d ih =>
      intro j hj hg
      have hjH : j < H := by omega
      have good' : ∀ h : Fin H, j + 1 ≤ h.val → fac (wipe d1 M w0) π τ h ≠ 0 :=
        fun h hh => hg h (by omega)
      have ih' := ih (j + 1) (by omega) good'
      by_cases hR : Reach d1 M j (τ ⟨j, hjH⟩).1
      · have hfwd : ∀ m (hm : j ≤ m) (hmH : m < H), Reach d1 M m (τ ⟨m, hmH⟩).1 := by
          intro m hm
          induction m, hm using Nat.le_induction with
          | base => intro _; exact hR
          | succ m hm ihm =>
            intro hmH
            have hr := ihm (by omega)
            have hf := hg ⟨m, by omega⟩ hm
            unfold fac at hf
            have hnw := right_ne_zero_of_mul hf
            rw [wipe_nextWeight] at hnw
            have hn' : m + 1 < H := hmH
            have hPne : M.P ⟨m, by omega⟩ (τ ⟨m, by omega⟩).1 (τ ⟨m, by omega⟩).2.1
                (τ ⟨m + 1, hn'⟩).1 ≠ 0 := by
              simpa [nextWeight, hn'] using hnw
            have hPpos := lt_of_le_of_ne ((hM.1 _ _ _).1 _) (Ne.symm hPne)
            exact Reach.step ⟨m, by omega⟩ _ _ _ hr hPpos
        have hfacM : ∀ h : Fin H, j ≤ h.val → fac M π τ h ≠ 0 := by
          intro h hh
          have hg' := hg h hh
          unfold fac at hg' ⊢
          rw [wipe_R_reach d1 M w0 h _ (hfwd h.val hh h.2), wipe_nextWeight] at hg'
          exact hg'
        obtain ⟨π'', τ'', hπ'', hne'', hsum⟩ :=
          glue d1 M rv (rv w0) hw0 hM j (τ ⟨j, hjH⟩).1 hR hjH τ π hπ rfl hfacM
        have := (hN π'' τ'' hπ'' hne'').2
        linarith
      · have hfj := hg ⟨j, hjH⟩ le_rfl
        unfold fac at hfj
        rw [wipe_R_unreach d1 M w0 ⟨j, hjH⟩ _ hR] at hfj
        have hw : (τ ⟨j, hjH⟩).2.2 = w0 := by
          by_contra hne'
          simp [hne'] at hfj
        rw [filter_split j hjH, hw]
        push_cast at ih'
        linarith
  have := claim (H - k.val) k.val (by have := k.2; omega) hgood
  have hk : 0 ≤ (k.val : ℝ) * rv w0 := mul_nonneg (Nat.cast_nonneg _) hμ0
  linarith

theorem exists_wipe [Nonempty A] [Nonempty W] {H : ℕ} (d1 : S → ℝ) (M : TabMDP S A W H)
    (rv : W → ℝ) (hrv : ∀ w, 0 ≤ rv w ∧ rv w ≤ 1) (hd : IsDist d1) (hM : IsTabMDP M)
    (hN : ∀ π τ, IsPolicy π → trajLaw d1 M π τ ≠ 0 →
      0 ≤ ∑ h : Fin H, rv (τ h).2.2 ∧ ∑ h : Fin H, rv (τ h).2.2 ≤ 1) :
    ∃ M' : TabMDP S A W H, IsTabMDP M' ∧ Suf rv M' ∧
      ∀ π τ, trajLaw d1 M' π τ = trajLaw d1 M π τ := by
  obtain ⟨w0, _, hw0⟩ := Finset.exists_min_image Finset.univ rv Finset.univ_nonempty
  exact ⟨wipe d1 M w0, wipe_isTab d1 M w0 hM,
    wipe_suf d1 M rv hrv hd hM hN w0 (fun w => hw0 w (Finset.mem_univ w)),
    fun π τ => wipe_trajLaw d1 M w0 hd hM π τ⟩

end wsuf

section alg

theorem cs_w {ι : Type*} [Fintype ι] (u x : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (∑ i, u i * x i) ^ 2 ≤ (∑ i, u i) * ∑ i, u i * x i ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (u i))
    (fun i => Real.sqrt (u i) * x i)
  have e1 : ∀ i, Real.sqrt (u i) * (Real.sqrt (u i) * x i) = u i * x i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hu i)]
  have e2 : ∀ i, Real.sqrt (u i) ^ 2 = u i := fun i => Real.sq_sqrt (hu i)
  have e3 : ∀ i, (Real.sqrt (u i) * x i) ^ 2 = u i * x i ^ 2 := fun i => by
    rw [mul_pow, e2]
  simp only [e1, e2, e3] at this
  exact this

theorem pair_bound {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (q r : ι → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (hr0 : ∀ i, 0 ≤ r i) :
    ∑ i, ∑ j, w i * w j * (q j * r j + q j * r i) ≤
      2 * Real.sqrt (∑ i, ∑ j, w i * w j * (q j * r i ^ 2)) := by
  set Q := ∑ j, w j * q j with hQ
  set E := ∑ i, w i * r i ^ 2 with hE
  set a := ∑ j, w j * (q j * r j) with ha
  set m := ∑ i, w i * r i with hm
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun j _ => mul_nonneg (hw0 j) (hq0 j))
  have hQ1 : Q ≤ 1 := by
    calc Q ≤ ∑ j, w j := Finset.sum_le_sum (fun j _ => by
          have := mul_le_mul_of_nonneg_left (hq1 j) (hw0 j); linarith)
      _ = 1 := hw1
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (sq_nonneg _))
  have h1 : ∑ i, ∑ j, w i * w j * (q j * r j + q j * r i) = a + Q * m := by
    have t1 : ∑ i, ∑ j, w i * w j * (q j * r j) = a := by
      calc ∑ i, ∑ j, w i * w j * (q j * r j) = ∑ i, w i * a := by
            apply Finset.sum_congr rfl; intro i _
            rw [ha, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _; ring
        _ = a := by rw [← Finset.sum_mul, hw1, one_mul]
    have t2 : ∑ i, ∑ j, w i * w j * (q j * r i) = Q * m := by
      rw [hQ, hm, Finset.sum_mul_sum, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    calc ∑ i, ∑ j, w i * w j * (q j * r j + q j * r i)
        = ∑ i, ∑ j, (w i * w j * (q j * r j) + w i * w j * (q j * r i)) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _; ring
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          rw [t1, t2]
  have h2 : ∑ i, ∑ j, w i * w j * (q j * r i ^ 2) = Q * E := by
    rw [hQ, hE, Finset.sum_mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h1, h2]
  -- a^2 ≤ Q * E
  have hsa : a ^ 2 ≤ Q * E := by
    have cs := cs_w (fun j => w j * q j) r (fun j => mul_nonneg (hw0 j) (hq0 j))
    have e : ∑ j, w j * q j * r j = a := by
      rw [ha]; apply Finset.sum_congr rfl; intro j _; ring
    rw [e] at cs
    have h3 : ∑ j, w j * q j * r j ^ 2 ≤ E := by
      rw [hE]
      apply Finset.sum_le_sum; intro j _
      have := mul_le_mul_of_nonneg_left (hq1 j) (mul_nonneg (hw0 j) (sq_nonneg (r j)))
      nlinarith
    calc a ^ 2 ≤ Q * ∑ j, w j * q j * r j ^ 2 := cs
      _ ≤ Q * E := mul_le_mul_of_nonneg_left h3 hQ0
  have hsm : m ^ 2 ≤ E := by
    have cs := cs_w w r hw0
    rw [hw1, one_mul] at cs
    exact cs
  have hsb : (Q * m) ^ 2 ≤ Q * E := by
    calc (Q * m) ^ 2 = Q ^ 2 * m ^ 2 := by ring
      _ ≤ Q ^ 2 * E := mul_le_mul_of_nonneg_left hsm (sq_nonneg _)
      _ ≤ Q * E := by nlinarith [mul_nonneg hQ0 hE0]
  have f1 : a ≤ Real.sqrt (Q * E) := le_trans (le_abs_self a) (Real.abs_le_sqrt hsa)
  have f2 : Q * m ≤ Real.sqrt (Q * E) := le_trans (le_abs_self _) (Real.abs_le_sqrt hsb)
  linarith

theorem regroup4 {ι L T : Type*} [Fintype ι] [Fintype L] [Fintype T] (F : ι → ι → L → T → ℝ) :
    ∑ i, ∑ j, ∑ ℓ, ∑ t, F i j ℓ t = ∑ ℓ, ∑ t, ∑ i, ∑ j, F i j ℓ t := by
  calc ∑ i, ∑ j, ∑ ℓ, ∑ t, F i j ℓ t
      = ∑ i, ∑ ℓ, ∑ j, ∑ t, F i j ℓ t :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ ℓ, ∑ i, ∑ j, ∑ t, F i j ℓ t := Finset.sum_comm
    _ = ∑ ℓ, ∑ i, ∑ t, ∑ j, F i j ℓ t :=
        Finset.sum_congr rfl (fun ℓ _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _ = ∑ ℓ, ∑ t, ∑ i, ∑ j, F i j ℓ t :=
        Finset.sum_congr rfl (fun ℓ _ => Finset.sum_comm)

theorem alg_main {ι L T : Type*} [Fintype ι] [Fintype L] [Fintype T]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (q r : ι → L → T → ℝ)
    (hq0 : ∀ j ℓ t, 0 ≤ q j ℓ t) (hq1 : ∀ j ℓ t, q j ℓ t ≤ 1) (hr0 : ∀ i ℓ t, 0 ≤ r i ℓ t)
    (V : ι → ι → ℝ) (Vb : ι → ℝ) (D : ι → ι → ℝ) (hD0 : ∀ i j, 0 ≤ D i j)
    (c γ : ℝ) (hc : 0 ≤ c) (hγ : 0 < γ)
    (hsim : ∀ i j, |V i j - Vb j| ≤ c * ∑ ℓ, ∑ t, q j ℓ t * r i ℓ t)
    (hlayer : ∀ i j ℓ, ∑ t, q j ℓ t * (r i ℓ t) ^ 2 ≤ 4 * D i j) :
    ∑ i, w i * ∑ j, w j * (V i i - V i j - γ * D i j) ≤
      4 * c ^ 2 * (Fintype.card L : ℝ) ^ 2 * (Fintype.card T : ℝ) / γ := by
  classical
  set Y := ∑ i, ∑ j, w i * w j * D i j with hY
  have hY0 : 0 ≤ Y := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hw0 i) (hw0 j)) (hD0 i j)))
  -- symmetrize
  have sw1 : ∑ i, ∑ j, w i * w j * V i i = ∑ i, w i * V i i := by
    apply Finset.sum_congr rfl; intro i _
    calc ∑ j, w i * w j * V i i = w i * V i i * ∑ j, w j := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ = _ := by rw [hw1, mul_one]
  have sw2 : ∑ i, ∑ j, w i * w j * V j j = ∑ j, w j * V j j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    calc ∑ i, w i * w j * V j j = (∑ i, w i) * (w j * V j j) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := by rw [hw1, one_mul]
  have h0 : ∑ i, w i * ∑ j, w j * (V i i - V i j - γ * D i j) =
      ∑ i, ∑ j, w i * w j * (V j j - V i j) - γ * Y := by
    have e1 : ∑ i, w i * ∑ j, w j * (V i i - V i j - γ * D i j) =
        ∑ i, ∑ j, w i * w j * V i i - ∑ i, ∑ j, w i * w j * V i j - γ * Y := by
      have per : ∀ i, w i * ∑ j, w j * (V i i - V i j - γ * D i j) =
          ∑ j, w i * w j * V i i - ∑ j, w i * w j * V i j - γ * ∑ j, w i * w j * D i j := by
        intro i
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [Finset.sum_congr rfl (fun i _ => per i)]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hY]
    have e2 : ∑ i, ∑ j, w i * w j * (V j j - V i j) =
        ∑ i, ∑ j, w i * w j * V j j - ∑ i, ∑ j, w i * w j * V i j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [e1, e2, sw1, sw2]
  -- pointwise bound
  have hpt : ∀ i j, V j j - V i j ≤ c * ∑ ℓ, ∑ t, (q j ℓ t * r j ℓ t + q j ℓ t * r i ℓ t) := by
    intro i j
    have a1 := hsim j j
    have a2 := hsim i j
    have b1 := le_abs_self (V j j - Vb j)
    have b2 := neg_abs_le (V i j - Vb j)
    have e : ∑ ℓ, ∑ t, (q j ℓ t * r j ℓ t + q j ℓ t * r i ℓ t) =
        ∑ ℓ, ∑ t, q j ℓ t * r j ℓ t + ∑ ℓ, ∑ t, q j ℓ t * r i ℓ t := by
      simp only [Finset.sum_add_distrib]
    rw [e]
    nlinarith
  set O : L → T → ℝ := fun ℓ t => ∑ i, ∑ j, w i * w j * (q j ℓ t * r i ℓ t ^ 2) with hO
  have hO0 : ∀ ℓ t, 0 ≤ O ℓ t := fun ℓ t =>
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (hw0 i) (hw0 j)) (mul_nonneg (hq0 j ℓ t) (sq_nonneg _))))
  have hstep1 : ∑ i, ∑ j, w i * w j * (V j j - V i j) ≤
      c * ∑ ℓ, ∑ t, 2 * Real.sqrt (O ℓ t) := by
    calc ∑ i, ∑ j, w i * w j * (V j j - V i j)
        ≤ ∑ i, ∑ j, w i * w j * (c * ∑ ℓ, ∑ t, (q j ℓ t * r j ℓ t + q j ℓ t * r i ℓ t)) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hpt i j) (mul_nonneg (hw0 i) (hw0 j))
      _ = c * ∑ i, ∑ j, ∑ ℓ, ∑ t, w i * w j * (q j ℓ t * r j ℓ t + q j ℓ t * r i ℓ t) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro ℓ _
          apply Finset.sum_congr rfl; intro t _; ring
      _ = c * ∑ ℓ, ∑ t, ∑ i, ∑ j, w i * w j * (q j ℓ t * r j ℓ t + q j ℓ t * r i ℓ t) := by
          rw [regroup4]
      _ ≤ c * ∑ ℓ, ∑ t, 2 * Real.sqrt (O ℓ t) := by
          apply mul_le_mul_of_nonneg_left _ hc
          apply Finset.sum_le_sum; intro ℓ _
          apply Finset.sum_le_sum; intro t _
          exact pair_bound w hw0 hw1 (fun j => q j ℓ t) (fun i => r i ℓ t)
            (fun j => hq0 j ℓ t) (fun j => hq1 j ℓ t) (fun i => hr0 i ℓ t)
  -- per layer bound
  set τ := Real.sqrt (Fintype.card T : ℝ) with hτ
  set s := Real.sqrt Y with hs
  have hτ2 : τ ^ 2 = (Fintype.card T : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs2 : s ^ 2 = Y := Real.sq_sqrt hY0
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hlay : ∀ ℓ, ∑ t, Real.sqrt (O ℓ t) ≤ 2 * τ * s := by
    intro ℓ
    have hsumO : ∑ t, O ℓ t ≤ 4 * Y := by
      calc ∑ t, O ℓ t = ∑ i, ∑ j, w i * w j * ∑ t, q j ℓ t * r i ℓ t ^ 2 := by
            simp only [hO]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro i _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _
            rw [Finset.mul_sum]
        _ ≤ ∑ i, ∑ j, w i * w j * (4 * D i j) := by
            apply Finset.sum_le_sum; intro i _
            apply Finset.sum_le_sum; intro j _
            exact mul_le_mul_of_nonneg_left (hlayer i j ℓ) (mul_nonneg (hw0 i) (hw0 j))
        _ = 4 * Y := by
            rw [hY, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _; ring
    have cs := cs_w (fun _ : T => (1 : ℝ)) (fun t => Real.sqrt (O ℓ t)) (fun _ => zero_le_one)
    simp only [one_mul] at cs
    have e1 : ∑ t, Real.sqrt (O ℓ t) ^ 2 = ∑ t, O ℓ t :=
      Finset.sum_congr rfl (fun t _ => Real.sq_sqrt (hO0 ℓ t))
    rw [e1] at cs
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at cs
    have hX0 : 0 ≤ ∑ t, Real.sqrt (O ℓ t) := Finset.sum_nonneg (fun t _ => Real.sqrt_nonneg _)
    have hle : (∑ t, Real.sqrt (O ℓ t)) ^ 2 ≤ (2 * τ * s) ^ 2 := by
      calc _ ≤ (Fintype.card T : ℝ) * ∑ t, O ℓ t := cs
        _ ≤ (Fintype.card T : ℝ) * (4 * Y) :=
            mul_le_mul_of_nonneg_left hsumO (Nat.cast_nonneg _)
        _ = (2 * τ * s) ^ 2 := by rw [mul_pow, mul_pow, hτ2, hs2]; ring
    have h2 : 0 ≤ 2 * τ * s := by positivity
    nlinarith [sq_nonneg (∑ t, Real.sqrt (O ℓ t) - 2 * τ * s)]
  have hstep2 : ∑ ℓ, ∑ t, 2 * Real.sqrt (O ℓ t) ≤ (Fintype.card L : ℝ) * (4 * τ * s) := by
    calc ∑ ℓ, ∑ t, 2 * Real.sqrt (O ℓ t) = ∑ ℓ, 2 * ∑ t, Real.sqrt (O ℓ t) := by
          apply Finset.sum_congr rfl; intro ℓ _; rw [Finset.mul_sum]
      _ ≤ ∑ _ℓ : L, 2 * (2 * τ * s) := by
          apply Finset.sum_le_sum; intro ℓ _
          have := hlay ℓ; linarith
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [h0, ← hs2]
  set Lc := (Fintype.card L : ℝ) with hLc
  have hfin : c * (Lc * (4 * τ * s)) - γ * s ^ 2 ≤ 4 * c ^ 2 * Lc ^ 2 * (Fintype.card T : ℝ) / γ := by
    rw [← hτ2, le_div_iff₀ hγ]
    nlinarith [sq_nonneg (γ * s - 2 * c * Lc * τ)]
  have := mul_le_mul_of_nonneg_left hstep2 hc
  linarith

end alg

end PCIGWAux

open StatComplexityDM.TabularPS in
theorem solution {S A W I : Type*}
    [Fintype S] [Fintype A] [Fintype W] [Fintype I]
    [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (Ms : I → TabMDP S A W H) (w : I → ℝ)
    (Mbar : TabMDP S A W H)
    (piStar : TabMDP S A W H → Policy S A H) (γ : ℝ)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1) (hw : StatComplexityDM.LowerBound.IsDist w)
    (hMs : ∀ i, IsTabMDP (Ms i) ∧ RewardsNormalized d1 rv (Ms i))
    (hMbar : IsTabMDP Mbar ∧ RewardsNormalized d1 rv Mbar)
    (hpiStar : ∀ M, IsTabMDP M → RewardsNormalized d1 rv M →
      IsPolicy (piStar M) ∧
        ∀ π, IsPolicy π → value d1 rv M π ≤ value d1 rv M (piStar M))
    (hγ : 0 < γ) :
    ∑ i, w i * ∑ j, w j *
      (value d1 rv (Ms i) (piStar (Ms i)) -
        value d1 rv (Ms i) (piStar (Ms j)) -
        γ * FoundationsRL.GeneralDM.hellingerSq
          (trajLaw d1 (Ms i) (piStar (Ms j)))
          (trajLaw d1 Mbar (piStar (Ms j)))) ≤
      26 * (H : ℝ) ^ 2 * Fintype.card S * Fintype.card A / γ := by
  classical
  have hπ : ∀ j, IsPolicy (piStar (Ms j)) := fun j => (hpiStar (Ms j) (hMs j).1 (hMs j).2).1
  have hex : ∀ i, ∃ N : TabMDP S A W H, IsTabMDP N ∧ PCIGWAux.Suf rv N ∧
      ∀ π τ, trajLaw d1 N π τ = trajLaw d1 (Ms i) π τ :=
    fun i => PCIGWAux.exists_wipe d1 (Ms i) rv (hMs i).2.1 hd1 (hMs i).1 (hMs i).2.2
  choose N hN1 hN2 hN3 using hex
  have hval : ∀ i π', value d1 rv (N i) π' = value d1 rv (Ms i) π' := by
    intro i π'
    unfold value
    simp_rw [hN3 i π']
  have hH2 : ∀ i π', FoundationsRL.GeneralDM.hellingerSq (trajLaw d1 (N i) π') (trajLaw d1 Mbar π') =
      FoundationsRL.GeneralDM.hellingerSq (trajLaw d1 (Ms i) π') (trajLaw d1 Mbar π') := by
    intro i π'
    have : trajLaw d1 (N i) π' = trajLaw d1 (Ms i) π' := funext (hN3 i π')
    rw [this]
  have hocc1 : ∀ j (ℓ : Fin H) (s : S) (a : A),
      occ d1 Mbar (piStar (Ms j)) ℓ s a ≤ 1 := by
    intro j ℓ s a
    have h1 := PCIGWAux.occ_sum d1 Mbar (piStar (Ms j)) hd1 hMbar.1 (hπ j) ℓ
    have h2 : occ d1 Mbar (piStar (Ms j)) ℓ s a ≤ ∑ a', occ d1 Mbar (piStar (Ms j)) ℓ s a' :=
      Finset.single_le_sum (f := fun a' => occ d1 Mbar (piStar (Ms j)) ℓ s a')
        (fun a' _ => PCIGWAux.occ_nonneg d1 Mbar (piStar (Ms j)) hd1 hMbar.1 (hπ j) ℓ s a')
        (Finset.mem_univ a)
    have h3 : ∑ a', occ d1 Mbar (piStar (Ms j)) ℓ s a' ≤
        ∑ s', ∑ a', occ d1 Mbar (piStar (Ms j)) ℓ s' a' :=
      Finset.single_le_sum (f := fun s' => ∑ a', occ d1 Mbar (piStar (Ms j)) ℓ s' a')
        (fun s' _ => Finset.sum_nonneg (fun a' _ =>
          PCIGWAux.occ_nonneg d1 Mbar (piStar (Ms j)) hd1 hMbar.1 (hπ j) ℓ s' a'))
        (Finset.mem_univ s)
    linarith
  have hlh0 : ∀ i (ℓ : Fin H) (s : S) (a : A), 0 ≤ localHellinger (N i) Mbar ℓ s a := by
    intro i ℓ s a
    unfold localHellinger
    exact add_nonneg (by split_ifs; exact PCIGWAux.hellingerSq_nonneg' _ _; exact le_refl _)
      (PCIGWAux.hellingerSq_nonneg' _ _)
  have key := PCIGWAux.alg_main (ι := I) (L := Fin H) (T := S × A) w hw.1 hw.2
    (fun j ℓ t => occ d1 Mbar (piStar (Ms j)) ℓ t.1 t.2)
    (fun i ℓ t => Real.sqrt (localHellinger (N i) Mbar ℓ t.1 t.2))
    (fun j ℓ t => PCIGWAux.occ_nonneg d1 Mbar (piStar (Ms j)) hd1 hMbar.1 (hπ j) ℓ t.1 t.2)
    (fun j ℓ t => hocc1 j ℓ t.1 t.2)
    (fun i ℓ t => Real.sqrt_nonneg _)
    (fun i j => value d1 rv (Ms i) (piStar (Ms j)))
    (fun j => value d1 rv Mbar (piStar (Ms j)))
    (fun i j => FoundationsRL.GeneralDM.hellingerSq (trajLaw d1 (Ms i) (piStar (Ms j)))
      (trajLaw d1 Mbar (piStar (Ms j))))
    (fun i j => PCIGWAux.hellingerSq_nonneg' _ _)
    (Real.sqrt 2) γ (Real.sqrt_nonneg _) hγ
    (by
      intro i j
      have := PCIGWAux.sim rv (hMbar.2.1) H d1 (N i) Mbar (piStar (Ms j)) hd1 (hN1 i) hMbar.1
        (hπ j) (hN2 i)
      rw [hval i (piStar (Ms j))] at this
      simp only [Fintype.sum_prod_type]
      exact this)
    (by
      intro i j ℓ
      have := PCIGWAux.layer H d1 d1 (N i) Mbar (piStar (Ms j)) ℓ 1 1 zero_le_one zero_le_one hd1 hd1
        (hN1 i) hMbar.1 (hπ j)
      simp only [one_mul, one_pow] at this
      have h4 : ∑ t : S × A, occ d1 Mbar (piStar (Ms j)) ℓ t.1 t.2 *
          Real.sqrt (localHellinger (N i) Mbar ℓ t.1 t.2) ^ 2 =
          ∑ s, ∑ a, occ d1 Mbar (piStar (Ms j)) ℓ s a * localHellinger (N i) Mbar ℓ s a := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl; intro s _
        apply Finset.sum_congr rfl; intro a _
        rw [Real.sq_sqrt (hlh0 i ℓ s a)]
      have h5 : ∑ τ, (Real.sqrt (trajLaw d1 (N i) (piStar (Ms j)) τ) -
            Real.sqrt (trajLaw d1 Mbar (piStar (Ms j)) τ)) ^ 2 =
          FoundationsRL.GeneralDM.hellingerSq (trajLaw d1 (Ms i) (piStar (Ms j)))
            (trajLaw d1 Mbar (piStar (Ms j))) := by
        rw [← hH2 i (piStar (Ms j))]
        rfl
      show ∑ t : S × A, occ d1 Mbar (piStar (Ms j)) ℓ t.1 t.2 *
          Real.sqrt (localHellinger (N i) Mbar ℓ t.1 t.2) ^ 2 ≤ 4 * _
      rw [h4]
      rw [h5] at this
      linarith)
  refine le_trans key ?_
  rw [Fintype.card_fin, Fintype.card_prod]
  push_cast
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [h2]
  have hx : 0 ≤ (H : ℝ) ^ 2 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) := by positivity
  rw [show 26 * (H : ℝ) ^ 2 * Fintype.card S * Fintype.card A =
    26 * ((H : ℝ) ^ 2 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ)) by ring,
    show 4 * 2 * (H : ℝ) ^ 2 * ((Fintype.card S : ℝ) * (Fintype.card A : ℝ)) =
    8 * ((H : ℝ) ^ 2 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ)) by ring]
  apply div_le_div_of_nonneg_right _ hγ.le
  linarith
