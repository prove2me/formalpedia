-- Prove2me | solution 1 for StatComplexityDM.PCIGW.pcigw_dec_tabular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T04:13:12.786249+00:00
-- url     : https://prove2.me/submissions/064f27b3-6818-4d91-ac84-987ca62691c5

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_Algorithm

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PCIGWAux

open StatComplexityDM.TabularPS StatComplexityDM.LowerBound FoundationsRL.GeneralDM StatComplexityDM.PCIGW

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
    |∑ y, (P y - Q y) * ψ y| ≤ 2 * Real.sqrt (hellingerSq P Q) := by
  have e : ∀ y, (P y - Q y) * ψ y =
      (Real.sqrt (P y) - Real.sqrt (Q y)) * ((Real.sqrt (P y) + Real.sqrt (Q y)) * ψ y) := by
    intro y
    have a1 := Real.sq_sqrt (hP.1 y)
    have a2 := Real.sq_sqrt (hQ.1 y)
    calc (P y - Q y) * ψ y = (Real.sqrt (P y) ^ 2 - Real.sqrt (Q y) ^ 2) * ψ y := by rw [a1, a2]
      _ = _ := by ring
  simp_rw [e]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun y => Real.sqrt (P y) - Real.sqrt (Q y))
    (fun y => (Real.sqrt (P y) + Real.sqrt (Q y)) * ψ y)
  have hb : ∑ y, ((Real.sqrt (P y) + Real.sqrt (Q y)) * ψ y) ^ 2 ≤ 4 := by
    calc ∑ y, ((Real.sqrt (P y) + Real.sqrt (Q y)) * ψ y) ^ 2
        ≤ ∑ y, (P y + Q y + 2 * (Real.sqrt (P y) * Real.sqrt (Q y))) := by
          apply Finset.sum_le_sum
          intro y _
          have a1 := Real.sq_sqrt (hP.1 y)
          have a2 := Real.sq_sqrt (hQ.1 y)
          have hψ : ψ y ^ 2 ≤ 1 := by nlinarith [h0 y, h1 y]
          have hs : 0 ≤ (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 := sq_nonneg _
          calc ((Real.sqrt (P y) + Real.sqrt (Q y)) * ψ y) ^ 2
              = (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 * ψ y ^ 2 := by ring
            _ ≤ (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 * 1 := by
                exact mul_le_mul_of_nonneg_left hψ hs
            _ = _ := by nlinarith
      _ = 2 + 2 * aff P Q := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hP.2, hQ.2, ← Finset.mul_sum]
          unfold aff
          ring
      _ ≤ 4 := by linarith [aff_le_one P Q hP hQ]
  have hD : 0 ≤ hellingerSq P Q := hellingerSq_nonneg' P Q
  have hsq : (∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) *
      ((Real.sqrt (P y) + Real.sqrt (Q y)) * ψ y)) ^ 2 ≤ 4 * hellingerSq P Q := by
    calc _ ≤ (∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2) *
          ∑ y, ((Real.sqrt (P y) + Real.sqrt (Q y)) * ψ y) ^ 2 := cs
      _ = hellingerSq P Q * ∑ y, ((Real.sqrt (P y) + Real.sqrt (Q y)) * ψ y) ^ 2 := rfl
      _ ≤ hellingerSq P Q * 4 := mul_le_mul_of_nonneg_left hb hD
      _ = _ := by ring
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg (hellingerSq P Q)
  by_contra hcon
  have hcon := not_le.mp hcon
  nlinarith [abs_nonneg (∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) *
      ((Real.sqrt (P y) + Real.sqrt (Q y)) * ψ y)), sq_abs (∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) *
      ((Real.sqrt (P y) + Real.sqrt (Q y)) * ψ y))]

theorem one_sim {Y Z : Type*} [Fintype Y] [Fintype Z] (f f' : Y → ℝ) (g g' : Z → ℝ)
    (hf : IsDist f) (hf' : IsDist f') (hg : IsDist g) (hg' : IsDist g')
    (r : Y → ℝ) (v : Z → ℝ) (hr0 : ∀ y, 0 ≤ r y) (hr1 : ∀ y, r y ≤ 1)
    (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    |∑ y, (f y - f' y) * r y + ∑ z, (g z - g' z) * v z| ≤
      2 * Real.sqrt 2 * Real.sqrt (hellingerSq f f' + hellingerSq g g') := by
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
    _ ≤ 2 * Real.sqrt (hellingerSq f f') + 2 * Real.sqrt (hellingerSq g g') := add_le_add h1 h2
    _ ≤ _ := by nlinarith [h3]


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

/-- the suffix clause of `RewardsNormalized` -/
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
    2 * Real.sqrt 2 * Real.sqrt (localHellinger M Mb 0 s a) +
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
      2 * Real.sqrt 2 * ∑ h : Fin n, ∑ s, ∑ a,
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
        2 * Real.sqrt 2 * ∑ j : Fin n, ∑ s2, ∑ a2,
          occ (fun s' => Mb.P 0 s a s') (shiftM Mb) (shiftPi π) j s2 a2 *
            Real.sqrt (localHellinger (shiftM M) (shiftM Mb) j s2 a2) :=
      fun s a => ih _ (shiftM M) (shiftM Mb) (shiftPi π) (hMb.1 0 s a) hM' hMb' hπ' hS'
    have hc : ∀ s a, 0 ≤ d1 s * π 0 s a := fun s a => mul_nonneg (hd.1 s) ((hπ 0 s).1 a)
    have hbound : ∀ s a, |(∑ w, M.R 0 s a w * rv w +
          value (fun s' => M.P 0 s a s') rv (shiftM M) (shiftPi π)) -
        (∑ w, Mb.R 0 s a w * rv w +
          value (fun s' => Mb.P 0 s a s') rv (shiftM Mb) (shiftPi π))| ≤
        2 * Real.sqrt 2 * Real.sqrt (localHellinger M Mb 0 s a) +
          2 * Real.sqrt 2 * ∑ j : Fin n, ∑ s2, ∑ a2,
            occ (fun s' => Mb.P 0 s a s') (shiftM Mb) (shiftPi π) j s2 a2 *
              Real.sqrt (localHellinger (shiftM M) (shiftM Mb) j s2 a2) := by
      intro s a
      exact le_trans (layer_diff rv hrv M Mb π hM hMb hπ hS s a) (add_le_add_right (hih s a) _)
    rw [value_cons' rv d1 M π hM hπ, value_cons' rv d1 Mb π hMb hπ, Fin.sum_univ_succ,
      ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
    calc _ ≤ ∑ s, |∑ a, d1 s * π 0 s a * _| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, ∑ a, d1 s * π 0 s a *
          (2 * Real.sqrt 2 * Real.sqrt (localHellinger M Mb 0 s a) +
            2 * Real.sqrt 2 * ∑ j : Fin n, ∑ s2, ∑ a2,
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
          have e1 : ∑ s, ∑ a, d1 s * π 0 s a * (2 * Real.sqrt 2 * Real.sqrt (localHellinger M Mb 0 s a)) =
              2 * Real.sqrt 2 * ∑ s, ∑ a, occ d1 Mb π 0 s a *
                Real.sqrt (localHellinger M Mb 0 s a) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            rw [occ_zero d1 Mb π hd hMb hπ s a]
            ring
          have e2 : ∑ s, ∑ a, d1 s * π 0 s a * (2 * Real.sqrt 2 * ∑ j : Fin n, ∑ s2, ∑ a2,
                occ (fun s' => Mb.P 0 s a s') (shiftM Mb) (shiftPi π) j s2 a2 *
                  Real.sqrt (localHellinger (shiftM M) (shiftM Mb) j s2 a2)) =
              2 * Real.sqrt 2 * ∑ j : Fin n, ∑ s2, ∑ a2,
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

theorem amgm (κ r : ℝ) (hκ : 0 < κ) (hr : 0 ≤ r) :
    2 * Real.sqrt 2 * r ≤ κ * r ^ 2 + 2 / κ := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have e : κ * (κ * r ^ 2 + 2 / κ) = κ ^ 2 * r ^ 2 + 2 := by field_simp
  have : κ * (2 * Real.sqrt 2 * r) ≤ κ * (κ * r ^ 2 + 2 / κ) := by
    rw [e]
    nlinarith [sq_nonneg (κ * r - Real.sqrt 2)]
  exact le_of_mul_le_mul_left this hκ

theorem delta_bound {X : Type*} [Fintype X] (O δ : X → ℝ) (hO : ∀ x, 0 ≤ O x)
    (hδ : ∀ x, 0 ≤ δ x) (Δ κ Q Hr : ℝ) (hκ : 0 < κ)
    (h : |Δ| ≤ 2 * Real.sqrt 2 * ∑ x, O x * Real.sqrt (δ x))
    (hQ : ∑ x, O x * δ x ≤ Q) (hHr : ∑ x, O x ≤ Hr) :
    |Δ| ≤ κ * Q + 2 / κ * Hr := by
  have h1 : 2 * Real.sqrt 2 * ∑ x, O x * Real.sqrt (δ x) ≤
      κ * ∑ x, O x * δ x + 2 / κ * ∑ x, O x := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    have := amgm κ (Real.sqrt (δ x)) hκ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (hδ x)] at this
    nlinarith [mul_le_mul_of_nonneg_left this (hO x)]
  have h2 : 0 < 2 / κ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hQ hκ.le, mul_le_mul_of_nonneg_left hHr h2.le]

theorem lam_facts {Pol : Type*} (Ψ : Finset Pol) (piB : Pol) (hB : piB ∈ Ψ)
    (p g : Pol → ℝ) (lam η : ℝ) (hlam : 0 < lam) (hη : 0 < η)
    (hp : ∀ π, p π = 1 / (lam + η * g π)) (hg0 : ∀ π ∈ Ψ, 0 ≤ g π) (hgB : g piB = 0)
    (hsum : ∑ π ∈ Ψ, p π = 1) :
    1 ≤ lam ∧ lam ≤ Ψ.card ∧ ∑ π ∈ Ψ, p π * g π ≤ ((Ψ.card : ℝ) - 1) / η := by
  have hden : ∀ π ∈ Ψ, 0 < lam + η * g π := fun π hπ => by
    have := mul_nonneg hη.le (hg0 π hπ); linarith
  have hpnn : ∀ π ∈ Ψ, 0 ≤ p π := fun π hπ => by
    rw [hp]; exact le_of_lt (one_div_pos.2 (hden π hπ))
  have hpB : p piB = 1 / lam := by rw [hp, hgB]; simp
  have h1 : 1 / lam ≤ 1 := by
    rw [← hpB]; rw [← hsum]; exact Finset.single_le_sum hpnn hB
  have hlam1 : 1 ≤ lam := by
    rw [div_le_one hlam] at h1; exact h1
  have hple : ∀ π ∈ Ψ, p π ≤ 1 / lam := fun π hπ => by
    rw [hp]; apply one_div_le_one_div_of_le hlam
    have := mul_nonneg hη.le (hg0 π hπ); linarith
  have hcard : (1 : ℝ) ≤ Ψ.card / lam := by
    calc (1 : ℝ) = ∑ π ∈ Ψ, p π := hsum.symm
      _ ≤ ∑ π ∈ Ψ, 1 / lam := Finset.sum_le_sum hple
      _ = Ψ.card / lam := by simp [div_eq_mul_inv]
  have hlamle : lam ≤ Ψ.card := by
    rw [le_div_iff₀ hlam] at hcard; linarith
  have hkey : ∀ π ∈ Ψ, p π * g π = (1 - lam * p π) / η := fun π hπ => by
    have h3 : p π * (lam + η * g π) = 1 := by rw [hp]; field_simp [(hden π hπ).ne']
    field_simp
    nlinarith
  have hsumpg : ∑ π ∈ Ψ, p π * g π = ((Ψ.card : ℝ) - lam) / η := by
    rw [Finset.sum_congr rfl hkey, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    simp
  refine ⟨hlam1, hlamle, ?_⟩
  rw [hsumpg]
  exact div_le_div_of_nonneg_right (by linarith) hη.le

theorem assembly {Pol X : Type*} [Fintype X] [DecidableEq Pol]
    (Ψ : Finset Pol) (piB piM : Pol) (cov : X → Pol)
    (O : Pol → X → ℝ) (δ : X → ℝ) (D2 g p F Fb : Pol → ℝ)
    (H : ℕ) (hH : 1 ≤ H) (γ η lam Nr : ℝ) (hγ : 0 < γ)
    (hη : η = γ / (21 * (H : ℝ) ^ 2)) (hlam : 0 < lam)
    (hNr : Nr = Fintype.card X) (hNpos : 1 ≤ Nr)
    (hΨ : Ψ = Finset.univ.image cov ∪ {piB})
    (hp : ∀ π, p π = 1 / (lam + η * g π)) (hsum : ∑ π ∈ Ψ, p π = 1)
    (hgdef : ∀ π, g π = Fb piB - Fb π) (hg0 : ∀ π ∈ Ψ, 0 ≤ g π) (hgM : 0 ≤ g piM)
    (hO0 : ∀ π, (π ∈ Ψ ∨ π = piM) → ∀ x, 0 ≤ O π x)
    (hOsum : ∀ π, (π ∈ Ψ ∨ π = piM) → ∑ x, O π x ≤ H)
    (hOd : ∀ π, (π ∈ Ψ ∨ π = piM) → ∑ x, O π x * δ x ≤ 4 * H * D2 π)
    (hδ : ∀ x, 0 ≤ δ x) (hD2 : ∀ π, 0 ≤ D2 π)
    (hsim : ∀ π, (π ∈ Ψ ∨ π = piM) →
      |F π - Fb π| ≤ 2 * Real.sqrt 2 * ∑ x, O π x * Real.sqrt (δ x))
    (hcov : ∀ x, O piM x * (2 * Nr + η * g (cov x)) ≤ O (cov x) x * (2 * Nr + η * g piM)) :
    ∑ π ∈ Ψ, p π * (F piM - F π - γ * D2 π) ≤ 95 * (H : ℝ) ^ 2 * Nr / γ := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hBΨ : piB ∈ Ψ := by rw [hΨ]; simp
  have hcovΨ : ∀ x, cov x ∈ Ψ := fun x => by rw [hΨ]; simp
  have hgB : g piB = 0 := by rw [hgdef]; ring
  obtain ⟨hlam1, hlamle, hSpg⟩ := lam_facts Ψ piB hBΨ p g lam η hlam hη0 hp hg0 hgB hsum
  have hcardΨ : (Ψ.card : ℝ) ≤ Nr + 1 := by
    have : Ψ.card ≤ Fintype.card X + 1 := by
      rw [hΨ]
      calc _ ≤ (Finset.univ.image cov).card + ({piB} : Finset Pol).card :=
            Finset.card_union_le _ _
        _ ≤ Fintype.card X + 1 := by
            apply add_le_add
            · exact (Finset.card_image_le).trans (by simp)
            · simp
    rw [hNr]; exact_mod_cast this
  have hlam2 : lam ≤ 2 * Nr := by linarith
  have hden : ∀ π ∈ Ψ, 0 < lam + η * g π := fun π hπ => by
    have := mul_nonneg hη0.le (hg0 π hπ); linarith
  have hpnn : ∀ π ∈ Ψ, 0 ≤ p π := fun π hπ => by
    rw [hp]; exact le_of_lt (one_div_pos.2 (hden π hπ))
  set S2 := ∑ π ∈ Ψ, p π * D2 π with hS2def
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg (fun π hπ => mul_nonneg (hpnn π hπ) (hD2 π))
  -- bound for policies in Ψ
  have hbdΨ : ∀ π ∈ Ψ, |F π - Fb π| ≤ γ / 2 * D2 π + 16 * (H : ℝ) ^ 2 / γ := by
    intro π hπ
    have hκ : 0 < γ / (8 * H) := by positivity
    have := delta_bound (O π) δ (hO0 π (Or.inl hπ)) hδ (F π - Fb π) (γ / (8 * H))
      (4 * H * D2 π) H hκ (hsim π (Or.inl hπ)) (hOd π (Or.inl hπ)) (hOsum π (Or.inl hπ))
    refine le_trans this (le_of_eq ?_)
    field_simp
    ring
  -- bound for piM
  set G := g piM with hG
  have hA : 0 < 2 * Nr + η * G := by
    have := mul_nonneg hη0.le hgM; linarith
  have hB : ∀ x, 0 < 2 * Nr + η * g (cov x) := fun x => by
    have := mul_nonneg hη0.le (hg0 _ (hcovΨ x)); linarith
  have hwx : ∀ x, O piM x * δ x ≤ (2 * Nr + η * G) * (p (cov x) * (O (cov x) x * δ x)) := by
    intro x
    have hOc := hO0 (cov x) (Or.inl (hcovΨ x)) x
    have h1 : O piM x ≤ (2 * Nr + η * G) * (O (cov x) x / (2 * Nr + η * g (cov x))) := by
      rw [mul_div_assoc', le_div_iff₀ (hB x)]
      nlinarith [hcov x]
    have h2 : O (cov x) x / (2 * Nr + η * g (cov x)) ≤ p (cov x) * O (cov x) x := by
      have : p (cov x) * O (cov x) x = O (cov x) x / (lam + η * g (cov x)) := by
        rw [hp]; field_simp
      rw [this]
      exact div_le_div_of_nonneg_left hOc (hden _ (hcovΨ x)) (by linarith)
    have h3 : O piM x ≤ (2 * Nr + η * G) * (p (cov x) * O (cov x) x) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 hA.le)
    calc O piM x * δ x ≤ (2 * Nr + η * G) * (p (cov x) * O (cov x) x) * δ x :=
          mul_le_mul_of_nonneg_right h3 (hδ x)
      _ = _ := by ring
  have hfib : ∑ x, p (cov x) * (O (cov x) x * δ x) ≤ 4 * H * S2 := by
    have e : ∑ x, p (cov x) * (O (cov x) x * δ x) =
        ∑ π ∈ Finset.univ.image cov, ∑ x ∈ Finset.univ.filter (fun x => cov x = π),
          p π * (O π x * δ x) := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image cov)
        (g := cov) (fun x _ => Finset.mem_image_of_mem cov (Finset.mem_univ x))]
      apply Finset.sum_congr rfl
      intro π _
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.1 hx).2]
    have hsub : Finset.univ.image cov ⊆ Ψ := by rw [hΨ]; exact Finset.subset_union_left
    rw [e]
    calc _ ≤ ∑ π ∈ Finset.univ.image cov, p π * (4 * H * D2 π) := by
          apply Finset.sum_le_sum
          intro π hπ
          have hπΨ : π ∈ Ψ := hsub hπ
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (hpnn π hπΨ)
          calc _ ≤ ∑ x, O π x * δ x := by
                apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                intro x _ _
                exact mul_nonneg (hO0 π (Or.inl hπΨ) x) (hδ x)
            _ ≤ _ := hOd π (Or.inl hπΨ)
      _ ≤ ∑ π ∈ Ψ, p π * (4 * H * D2 π) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro π hπ _
          exact mul_nonneg (hpnn π hπ) (mul_nonneg (mul_nonneg (by norm_num) hH0.le) (hD2 π))
      _ = 4 * H * S2 := by
          rw [hS2def, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro π _; ring
  have hQ : ∑ x, O piM x * δ x ≤ (2 * Nr + η * G) * (4 * H * S2) := by
    calc _ ≤ ∑ x, (2 * Nr + η * G) * (p (cov x) * (O (cov x) x * δ x)) :=
          Finset.sum_le_sum (fun x _ => hwx x)
      _ = (2 * Nr + η * G) * ∑ x, p (cov x) * (O (cov x) x * δ x) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hfib hA.le
  have hbdM : |F piM - Fb piM| ≤ γ / 2 * S2 + 32 * (H : ℝ) ^ 2 * Nr / γ + 16 / 21 * G := by
    have hκ : 0 < γ / (8 * H * (2 * Nr + η * G)) := by positivity
    have := delta_bound (O piM) δ (hO0 piM (Or.inr rfl)) hδ (F piM - Fb piM)
      (γ / (8 * H * (2 * Nr + η * G))) ((2 * Nr + η * G) * (4 * H * S2)) H hκ
      (hsim piM (Or.inr rfl)) hQ (hOsum piM (Or.inr rfl))
    refine le_trans this (le_of_eq ?_)
    rw [hη]
    field_simp
    ring
  have hT : ∀ π ∈ Ψ, p π * (F piM - F π - γ * D2 π) =
      ((F piM - Fb piM) - G) * p π + p π * g π - p π * (F π - Fb π) - γ * (p π * D2 π) := by
    intro π _
    rw [hgdef π, hG, hgdef piM]
    ring
  rw [Finset.sum_congr rfl hT]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
  have hSΔ : -(∑ π ∈ Ψ, p π * (F π - Fb π)) ≤ γ / 2 * S2 + 16 * (H : ℝ) ^ 2 / γ := by
    calc -(∑ π ∈ Ψ, p π * (F π - Fb π)) = ∑ π ∈ Ψ, p π * (-(F π - Fb π)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro π _; ring
      _ ≤ ∑ π ∈ Ψ, p π * (γ / 2 * D2 π + 16 * (H : ℝ) ^ 2 / γ) := by
          apply Finset.sum_le_sum
          intro π hπ
          exact mul_le_mul_of_nonneg_left ((neg_le_abs _).trans (hbdΨ π hπ)) (hpnn π hπ)
      _ = γ / 2 * S2 + 16 * (H : ℝ) ^ 2 / γ := by
          have : ∀ π ∈ Ψ, p π * (γ / 2 * D2 π + 16 * (H : ℝ) ^ 2 / γ) =
              γ / 2 * (p π * D2 π) + 16 * (H : ℝ) ^ 2 / γ * p π := fun π _ => by ring
          rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, hsum, hS2def]
          ring
  have hSpg2 : ∑ π ∈ Ψ, p π * g π ≤ 21 * (H : ℝ) ^ 2 * Nr / γ := by
    refine hSpg.trans ?_
    calc ((Ψ.card : ℝ) - 1) / η ≤ Nr / η :=
          div_le_div_of_nonneg_right (by linarith) hη0.le
      _ = 21 * (H : ℝ) ^ 2 * Nr / γ := by rw [hη]; field_simp
  have hY : 0 ≤ (H : ℝ) ^ 2 / γ := by positivity
  have hYN := mul_le_mul_of_nonneg_left hNpos hY
  have e1 : 32 * (H : ℝ) ^ 2 * Nr / γ = 32 * ((H : ℝ) ^ 2 / γ * Nr) := by ring
  have e2 : 21 * (H : ℝ) ^ 2 * Nr / γ = 21 * ((H : ℝ) ^ 2 / γ * Nr) := by ring
  have e3 : 95 * (H : ℝ) ^ 2 * Nr / γ = 95 * ((H : ℝ) ^ 2 / γ * Nr) := by ring
  have e4 : 16 * (H : ℝ) ^ 2 / γ = 16 * ((H : ℝ) ^ 2 / γ) := by ring
  rw [e1] at hbdM
  rw [e2] at hSpg2
  rw [e4] at hSΔ
  rw [e3]
  have := le_abs_self (F piM - Fb piM)
  nlinarith [hgM, hS2]

end PCIGWAux

open StatComplexityDM.PCIGW in
theorem solution {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W]
    [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (Mbar : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H)
    (γ η lam : ℝ) (cover : Fin H → S → A → StatComplexityDM.TabularPS.Policy S A H)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1)
    (hMbar : StatComplexityDM.TabularPS.IsTabMDP Mbar ∧ RewardsNormalized d1 rv Mbar)
    (hpiStar : IsOptimalSelector d1 rv piStar)
    (hγ : 0 < γ) (hη : η = γ / (21 * (H : ℝ) ^ 2))
    (halg : IsPCIGW d1 rv Mbar piStar η cover lam) :
    ∀ M : StatComplexityDM.TabularPS.TabMDP S A W H,
      StatComplexityDM.TabularPS.IsTabMDP M → RewardsNormalized d1 rv M →
      (∑ π ∈ pcigwPsi Mbar piStar cover,
        pcigwWeight d1 rv Mbar piStar η lam π *
          (StatComplexityDM.TabularPS.value d1 rv M (piStar M) - StatComplexityDM.TabularPS.value d1 rv M π -
            γ * FoundationsRL.GeneralDM.hellingerSq
              (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 Mbar π))) ≤
        95 * (H : ℝ) ^ 3 * Fintype.card S * Fintype.card A / γ := by
  classical
  intro M hM hMn
  have hcovpol : ∀ x : Fin H × S × A,
      StatComplexityDM.TabularPS.IsPolicy (cover x.1 x.2.1 x.2.2) :=
    fun x => halg.1.1 x.1 x.2.1 x.2.2
  have hpB := (hpiStar Mbar hMbar.1 hMbar.2).1
  have hpM := (hpiStar M hM hMn).1
  have hΨ : pcigwPsi Mbar piStar cover =
      Finset.univ.image (fun x : Fin H × S × A => cover x.1 x.2.1 x.2.2) ∪ {piStar Mbar} := rfl
  have hΨpol : ∀ π ∈ pcigwPsi Mbar piStar cover, StatComplexityDM.TabularPS.IsPolicy π := by
    intro π hπ
    rw [hΨ, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hπ
    rcases hπ with ⟨x, _, rfl⟩ | rfl
    · exact hcovpol x
    · exact hpB
  have hpol : ∀ π, (π ∈ pcigwPsi Mbar piStar cover ∨ π = piStar M) →
      StatComplexityDM.TabularPS.IsPolicy π := by
    intro π h
    rcases h with h | rfl
    · exact hΨpol π h
    · exact hpM
  have hNr : ((H : ℝ) * Fintype.card S * Fintype.card A) =
      (Fintype.card (Fin H × S × A) : ℝ) := by
    simp [Fintype.card_prod]; ring
  have hNpos : (1 : ℝ) ≤ (H : ℝ) * Fintype.card S * Fintype.card A := by
    have h1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have h2 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
    have h3 : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr
  have hsumX : ∀ (f : Fin H → S → A → ℝ),
      ∑ x : Fin H × S × A, f x.1 x.2.1 x.2.2 = ∑ h, ∑ s, ∑ a, f h s a := by
    intro f
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
  have key := PCIGWAux.assembly (Pol := StatComplexityDM.TabularPS.Policy S A H)
    (X := Fin H × S × A) (pcigwPsi Mbar piStar cover) (piStar Mbar) (piStar M)
    (fun x => cover x.1 x.2.1 x.2.2)
    (fun π x => StatComplexityDM.TabularPS.occ d1 Mbar π x.1 x.2.1 x.2.2)
    (fun x => StatComplexityDM.TabularPS.localHellinger M Mbar x.1 x.2.1 x.2.2)
    (fun π => FoundationsRL.GeneralDM.hellingerSq
      (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 Mbar π))
    (gapBar d1 rv Mbar piStar) (pcigwWeight d1 rv Mbar piStar η lam)
    (StatComplexityDM.TabularPS.value d1 rv M) (StatComplexityDM.TabularPS.value d1 rv Mbar)
    H hH γ η lam ((H : ℝ) * Fintype.card S * Fintype.card A) hγ hη halg.2.1 hNr hNpos hΨ
    (fun π => rfl) halg.2.2 (fun π => rfl)
    (by
      intro π hπ
      have := (hpiStar Mbar hMbar.1 hMbar.2).2 π (hΨpol π hπ)
      show 0 ≤ StatComplexityDM.TabularPS.value d1 rv Mbar (piStar Mbar) -
        StatComplexityDM.TabularPS.value d1 rv Mbar π
      linarith)
    (by
      have := (hpiStar Mbar hMbar.1 hMbar.2).2 (piStar M) hpM
      show 0 ≤ StatComplexityDM.TabularPS.value d1 rv Mbar (piStar Mbar) -
        StatComplexityDM.TabularPS.value d1 rv Mbar (piStar M)
      linarith)
    (by
      intro π hπ x
      exact PCIGWAux.occ_nonneg d1 Mbar π hd1 hMbar.1 (hpol π hπ) x.1 x.2.1 x.2.2)
    (by
      intro π hπ
      show ∑ x : Fin H × S × A, StatComplexityDM.TabularPS.occ d1 Mbar π x.1 x.2.1 x.2.2 ≤ H
      rw [hsumX (fun h s a => StatComplexityDM.TabularPS.occ d1 Mbar π h s a)]
      have : ∀ h : Fin H, ∑ s, ∑ a, StatComplexityDM.TabularPS.occ d1 Mbar π h s a = 1 :=
        fun h => PCIGWAux.occ_sum d1 Mbar π hd1 hMbar.1 (hpol π hπ) h
      simp [this])
    (by
      intro π hπ
      show ∑ x : Fin H × S × A, StatComplexityDM.TabularPS.occ d1 Mbar π x.1 x.2.1 x.2.2 *
        StatComplexityDM.TabularPS.localHellinger M Mbar x.1 x.2.1 x.2.2 ≤ 4 * H *
          FoundationsRL.GeneralDM.hellingerSq
            (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 Mbar π)
      rw [hsumX (fun h s a => StatComplexityDM.TabularPS.occ d1 Mbar π h s a *
        StatComplexityDM.TabularPS.localHellinger M Mbar h s a)]
      have hl : ∀ h : Fin H, ∑ s, ∑ a, StatComplexityDM.TabularPS.occ d1 Mbar π h s a *
          StatComplexityDM.TabularPS.localHellinger M Mbar h s a ≤
          4 * FoundationsRL.GeneralDM.hellingerSq
            (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 Mbar π) := by
        intro h
        have := PCIGWAux.layer H d1 d1 M Mbar π h 1 1 zero_le_one zero_le_one hd1 hd1 hM hMbar.1
          (hpol π hπ)
        simp only [one_mul, one_pow] at this
        unfold FoundationsRL.GeneralDM.hellingerSq
        linarith
      calc _ ≤ ∑ h : Fin H, 4 * FoundationsRL.GeneralDM.hellingerSq
            (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 Mbar π) :=
            Finset.sum_le_sum (fun h _ => hl h)
        _ = _ := by simp; ring)
    (by
      intro x
      unfold StatComplexityDM.TabularPS.localHellinger
      exact add_nonneg (by split_ifs; exact PCIGWAux.hellingerSq_nonneg' _ _; exact le_refl _)
        (PCIGWAux.hellingerSq_nonneg' _ _))
    (fun π => PCIGWAux.hellingerSq_nonneg' _ _)
    (by
      intro π hπ
      have := PCIGWAux.sim rv hMn.1 H d1 M Mbar π hd1 hM hMbar.1 (hpol π hπ) hMn.2.2
      show |StatComplexityDM.TabularPS.value d1 rv M π - StatComplexityDM.TabularPS.value d1 rv Mbar π| ≤
        2 * Real.sqrt 2 * ∑ x : Fin H × S × A, StatComplexityDM.TabularPS.occ d1 Mbar π x.1 x.2.1 x.2.2 *
          Real.sqrt (StatComplexityDM.TabularPS.localHellinger M Mbar x.1 x.2.1 x.2.2)
      rw [hsumX (fun h s a => StatComplexityDM.TabularPS.occ d1 Mbar π h s a *
        Real.sqrt (StatComplexityDM.TabularPS.localHellinger M Mbar h s a))]
      exact this)
    (by
      intro x
      have := halg.1.2 x.1 x.2.1 x.2.2 (piStar M) hpM
      show StatComplexityDM.TabularPS.occ d1 Mbar (piStar M) x.1 x.2.1 x.2.2 *
          (2 * ((H : ℝ) * Fintype.card S * Fintype.card A) + η * gapBar d1 rv Mbar piStar (cover x.1 x.2.1 x.2.2)) ≤
        StatComplexityDM.TabularPS.occ d1 Mbar (cover x.1 x.2.1 x.2.2) x.1 x.2.1 x.2.2 *
          (2 * ((H : ℝ) * Fintype.card S * Fintype.card A) + η * gapBar d1 rv Mbar piStar (piStar M))
      have e : 2 * ((H : ℝ) * Fintype.card S * Fintype.card A) =
          2 * (H : ℝ) * Fintype.card S * Fintype.card A := by ring
      rw [e]
      exact this)
  refine le_trans key (le_of_eq ?_)
  ring
