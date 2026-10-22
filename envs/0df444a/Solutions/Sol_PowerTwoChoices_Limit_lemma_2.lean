-- Prove2me | solution 1 for PowerTwoChoices.Limit.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:44:35.577007+00:00
-- url     : https://prove2.me/submissions/34687060-e01e-4e47-abd7-e7c2020a9507

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

set_option autoImplicit false
open scoped ENNReal
open Filter Topology PowerTwoChoices.Limit

theorem solution (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    IsState (fixedPoint lam d) ∧
    (∀ i : ℕ, 1 ≤ i → drift lam d (fixedPoint lam d) i = 0) ∧
    Summable (fixedPoint lam d) ∧
    ∀ x : ℕ → ℝ, IsState x → (∀ i : ℕ, 1 ≤ i → drift lam d x i = 0) → Summable x →
      x = fixedPoint lam d := by
  have fp0 : fixedPoint lam d 0 = 1 := by simp [fixedPoint]
  have fps : ∀ i, fixedPoint lam d (i + 1) = lam * fixedPoint lam d i ^ d := by
    intro i
    unfold fixedPoint
    rw [← pow_mul, ← pow_succ']
    congr 1
    rw [Finset.sum_range_succ', Finset.sum_mul]
    simp [pow_succ]
  have fpnn : ∀ i, 0 ≤ fixedPoint lam d i := fun i => pow_nonneg hlam0.le _
  have fple : ∀ i, fixedPoint lam d i ≤ 1 := fun i => pow_le_one₀ hlam0.le hlam1.le
  have hstate : IsState (fixedPoint lam d) := by
    refine ⟨fp0, fpnn, ?_⟩
    apply antitone_nat_of_succ_le
    intro i
    rw [fps]
    have h1 : fixedPoint lam d i ^ d ≤ fixedPoint lam d i :=
      pow_le_of_le_one (fpnn i) (fple i) (by omega)
    have h2 : lam * fixedPoint lam d i ^ d ≤ fixedPoint lam d i ^ d := by
      have := pow_nonneg (fpnn i) d
      nlinarith
    linarith
  refine ⟨hstate, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    unfold drift
    simp only [Nat.add_sub_cancel]
    have e1 := fps j
    have e2 := fps (j + 1)
    rw [e2] at *
    nlinarith [e1, e2]
  · have hle : ∀ i, fixedPoint lam d i ≤ lam ^ i := by
      intro i
      unfold fixedPoint
      apply pow_le_pow_of_le_one hlam0.le hlam1.le
      calc i = ∑ k ∈ Finset.range i, 1 := by simp
        _ ≤ ∑ k ∈ Finset.range i, d ^ k :=
          Finset.sum_le_sum (fun k _ => Nat.one_le_pow _ _ (by omega))
    exact Summable.of_nonneg_of_le fpnn hle (summable_geometric_of_lt_one hlam0.le hlam1)
  · intro x hx hdr hsum
    obtain ⟨hx0, hxnn, hxanti⟩ := hx
    have hlim : Tendsto x atTop (𝓝 0) := hsum.tendsto_atTop_zero
    set w : ℕ → ℝ := fun k => x (k + 1) - lam * x k ^ d with hw
    have hwstep : ∀ k, w (k + 1) = w k := by
      intro k
      have := hdr (k + 1) (by omega)
      unfold drift at this
      simp only [Nat.add_sub_cancel] at this
      simp only [hw]
      linarith
    have hwconst : ∀ k, w k = w 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [hwstep, ih]
    have hwlim : Tendsto w atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => x (k + 1)) atTop (𝓝 0) :=
        (tendsto_add_atTop_iff_nat 1).2 hlim
      have h2 : Tendsto (fun k => x k ^ d) atTop (𝓝 0) := by
        simpa [zero_pow (by omega : d ≠ 0)] using hlim.pow d
      simpa [hw] using h1.sub (h2.const_mul lam)
    have hw0 : w 0 = 0 := by
      have : Tendsto w atTop (𝓝 (w 0)) := by
        have : w = fun _ => w 0 := funext hwconst
        rw [this]; exact tendsto_const_nhds
      exact tendsto_nhds_unique this hwlim
    have hrec : ∀ k, x (k + 1) = lam * x k ^ d := by
      intro k
      have := hwconst k
      rw [hw0] at this
      simp only [hw] at this
      linarith
    funext k
    induction k with
    | zero => rw [hx0, fp0]
    | succ k ih => rw [hrec, fps, ih]
