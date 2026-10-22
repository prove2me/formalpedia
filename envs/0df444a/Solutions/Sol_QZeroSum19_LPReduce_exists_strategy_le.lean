-- Prove2me | solution 1 for QZeroSum19.LPReduce.exists_strategy_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:21:59.162277+00:00
-- url     : https://prove2.me/submissions/327d06e2-6ca2-46c6-8f72-6abb22deb94a

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

set_option autoImplicit false
open Matrix
open QZeroSum19.LPReduce

theorem qz_row0 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inl 0) = ∑ j, y (Sum.inl j) + y (Sum.inr 0) - y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem qz_row1 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inl 1) = -∑ j, y (Sum.inl j) - y (Sum.inr 0) + y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem qz_row2 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inr (Sum.inl ())) =
      -(b ⬝ᵥ (fun j => y (Sum.inl j))) + α / R * y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem qz_row3 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R : ℝ) (y : Fin m ⊕ Fin 2 → ℝ) (i : Fin n) :
    (gameMatrix A b c α R *ᵥ y) (Sum.inr (Sum.inr i)) =
      (A *ᵥ (fun j => y (Sum.inl j))) i - c i / R * y (Sum.inr 1) := by
  simp [gameMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem qz_simplex {m : ℕ} (y : Fin m ⊕ Fin 2 → ℝ) (hy : y ∈ stdSimplex ℝ (Fin m ⊕ Fin 2)) :
    (∀ j, 0 ≤ y (Sum.inl j)) ∧ 0 ≤ y (Sum.inr 0) ∧ 0 ≤ y (Sum.inr 1) ∧
      ∑ j, y (Sum.inl j) + y (Sum.inr 0) + y (Sum.inr 1) = 1 := by
  obtain ⟨h0, h1⟩ := hy
  refine ⟨fun j => h0 _, h0 _, h0 _, ?_⟩
  rw [Fintype.sum_sum_type, Fin.sum_univ_two] at h1
  linarith

theorem qz_h_half {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (α R κ : ℝ) (y' : Fin m ⊕ Fin 2 → ℝ) (hy' : y' ∈ stdSimplex ℝ (Fin m ⊕ Fin 2))
    (hle : ∀ k, (gameMatrix A b c α R *ᵥ y') k ≤ 2 * κ) :
    |y' (Sum.inr 1) - 1 / 2| ≤ κ := by
  obtain ⟨-, -, -, hs⟩ := qz_simplex y' hy'
  have h0 := hle (Sum.inl 0)
  have h1 := hle (Sum.inl 1)
  rw [qz_row0] at h0
  rw [qz_row1] at h1
  rw [abs_le]
  constructor <;> linarith

theorem qz_gv_le {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) (y : κ → ℝ)
    (hy : y ∈ stdSimplex ℝ κ) :
    QZeroSum19.GK.gameValue M ≤ ⨆ i, (M *ᵥ y) i := by
  unfold QZeroSum19.GK.gameValue
  apply csInf_le
  · refine ⟨-(∑ i, ∑ j, |M i j|), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hz0, hz1⟩ := hz
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp only [Real.iSup_of_isEmpty]
      have : 0 ≤ ∑ i, ∑ j, |M i j| := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
      linarith
    · obtain ⟨i0⟩ := hι
      refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove i0)
      have h1 : |(M *ᵥ z) i0| ≤ ∑ j, |M i0 j| := by
        simp only [Matrix.mulVec, dotProduct]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (hz0 j)]
        have : z j ≤ 1 := by
          rw [← hz1]; exact Finset.single_le_sum (fun k _ => hz0 k) (Finset.mem_univ j)
        nlinarith [abs_nonneg (M i0 j)]
      have h2 : ∑ j, |M i0 j| ≤ ∑ i, ∑ j, |M i j| :=
        Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i0)
      have := neg_abs_le ((M *ᵥ z) i0)
      linarith
  · exact ⟨y, hy, rfl⟩

theorem qz_exists {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (M : Matrix ι κ ℝ) (t : ℝ) (ht : QZeroSum19.GK.gameValue M ≤ t) :
    ∃ y ∈ stdSimplex ℝ κ, ∀ k, (M *ᵥ y) k ≤ t := by
  have hne : (stdSimplex ℝ κ).Nonempty := ⟨(inferInstance : Nonempty (stdSimplex ℝ κ)).some.1, (inferInstance : Nonempty (stdSimplex ℝ κ)).some.2⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨y, hy⟩ := hne
    exact ⟨y, hy, fun k => isEmptyElim k⟩
  · have hcont : Continuous (fun y : κ → ℝ => ⨆ i, (M *ᵥ y) i) := by
      have : (fun y : κ → ℝ => ⨆ i, (M *ᵥ y) i) =
          fun y => Finset.univ.sup' Finset.univ_nonempty (fun i => (M *ᵥ y) i) := by
        funext y
        exact le_antisymm (ciSup_le fun i => Finset.le_sup' (fun i => (M *ᵥ y) i) (Finset.mem_univ i))
          (Finset.sup'_le _ _ fun i _ => le_ciSup (Set.finite_range _).bddAbove i)
      rw [this]
      refine Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => ?_)
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    obtain ⟨y0, hy0, hmin⟩ := (isCompact_stdSimplex ℝ κ).exists_isMinOn hne hcont.continuousOn
    have hleast : IsLeast ((fun y => ⨆ i, (M *ᵥ y) i) '' stdSimplex ℝ κ) (⨆ i, (M *ᵥ y0) i) := by
      refine ⟨⟨y0, hy0, rfl⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hmin hz
    have hval : QZeroSum19.GK.gameValue M = ⨆ i, (M *ᵥ y0) i := hleast.csInf_eq
    refine ⟨y0, hy0, fun k => ?_⟩
    rw [hval] at ht
    exact (le_ciSup (Set.finite_range _).bddAbove k).trans ht

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (M : Matrix ι κ ℝ) (t : ℝ) (ht : QZeroSum19.GK.gameValue M ≤ t) :
    ∃ y ∈ stdSimplex ℝ κ, ∀ k, (M *ᵥ y) k ≤ t := qz_exists M t ht
