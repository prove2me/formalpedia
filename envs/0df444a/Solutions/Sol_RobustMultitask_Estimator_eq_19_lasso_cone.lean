-- Prove2me | solution 1 for RobustMultitask.Estimator.eq_19_lasso_cone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:30:15.507126+00:00
-- url     : https://prove2.me/submissions/dc6ed747-e041-495f-9057-ebb25221c337

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Definitions.Def_RobustMultitask_Estimator_Alignment

open Matrix

open RobustMultitask.Estimator in
theorem solution {N d m : ℕ} (X : Matrix (Fin m) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (ζ : ℝ) (j : Fin N) (lam : ℝ)
    (e : Fin m → ℝ) (b βhat : Fin d → ℝ) (hm : 0 < m)
    (hH : (2 / (m : ℝ)) * linf (Xᵀ *ᵥ e) ≤ lam / 2)
    (hmin : IsLassoMinimizer X (X *ᵥ β j + e) lam b βhat) :
    (1 / (m : ℝ)) * l2sq (X *ᵥ (βhat - β j)) + lam / 2 * l1 (βhat - β j)
      ≤ 2 * lam * l1 (restrict (augSupport β βdag ζ j) (βhat - β j))
        + 2 * lam * l1 (restrict (poorlyAligned β βdag ζ) (b - βdag)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set δ := βhat - β j with hδ
  have hl2 : ∀ v w : Fin m → ℝ, l2sq (v - w) = l2sq v - 2 * (v ⬝ᵥ w) + l2sq w := by
    intro v w
    simp only [l2sq, dotProduct, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros; ring
  have hneg : l2sq (-e) = l2sq e := by simp [l2sq]
  have h1 := hmin (β j)
  unfold lassoObjective at h1
  have e1 : X *ᵥ βhat - (X *ᵥ β j + e) = X *ᵥ δ - e := by
    rw [hδ, Matrix.mulVec_sub]; abel
  have e2 : X *ᵥ β j - (X *ᵥ β j + e) = -e := by abel
  rw [e1, e2, hl2, hneg] at h1
  -- dot product bound
  have hdot : (X *ᵥ δ) ⬝ᵥ e ≤ linf (Xᵀ *ᵥ e) * l1 δ := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    unfold l1 dotProduct
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb : |(Xᵀ *ᵥ e) i| ≤ linf (Xᵀ *ᵥ e) :=
      le_ciSup (Set.finite_range (fun i => |(Xᵀ *ᵥ e) i|)).bddAbove i
    calc (Xᵀ *ᵥ e) i * δ i ≤ |(Xᵀ *ᵥ e) i * δ i| := le_abs_self _
      _ = |(Xᵀ *ᵥ e) i| * |δ i| := abs_mul _ _
      _ ≤ linf (Xᵀ *ᵥ e) * |δ i| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hlinf0 : 0 ≤ linf (Xᵀ *ᵥ e) := Real.iSup_nonneg (fun i => abs_nonneg _)
  have hlam : 0 ≤ lam := by
    have : 0 ≤ (2 / (m : ℝ)) * linf (Xᵀ *ᵥ e) := mul_nonneg (by positivity) hlinf0
    linarith
  have hl1δ : 0 ≤ l1 δ := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hcross : (1 / (m : ℝ)) * (2 * ((X *ᵥ δ) ⬝ᵥ e)) ≤ lam / 2 * l1 δ := by
    have := mul_le_mul_of_nonneg_right hH hl1δ
    have h2 : (1 / (m : ℝ)) * (2 * ((X *ᵥ δ) ⬝ᵥ e)) ≤ (2 / (m : ℝ)) * linf (Xᵀ *ᵥ e) * l1 δ := by
      rw [show (1 / (m : ℝ)) * (2 * ((X *ᵥ δ) ⬝ᵥ e)) = (2 / (m : ℝ)) * ((X *ᵥ δ) ⬝ᵥ e) by ring,
        mul_assoc]
      exact mul_le_mul_of_nonneg_left hdot (by positivity)
    linarith
  -- coordinatewise cone bound
  have hcoord : l1 δ + l1 (β j - b) - l1 (βhat - b) ≤
      2 * l1 (restrict (augSupport β βdag ζ j) δ) +
        2 * l1 (restrict (poorlyAligned β βdag ζ) (b - βdag)) := by
    unfold l1
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    simp only [Pi.sub_apply, restrict, hδ]
    by_cases hi : i ∈ augSupport β βdag ζ j
    · rw [if_pos hi]
      have t1 := abs_sub_le (β j i) (βhat i) (b i)
      have t2 : |β j i - βhat i| = |βhat i - β j i| := abs_sub_comm _ _
      have t3 : 0 ≤ |if i ∈ poorlyAligned β βdag ζ then b i - βdag i else 0| := abs_nonneg _
      linarith
    · rw [if_neg hi]
      have hp : i ∈ poorlyAligned β βdag ζ := by
        by_contra hp
        apply hi
        unfold augSupport wellAligned
        exact Finset.mem_union_left _ (Finset.mem_compl.mpr hp)
      have hβ : β j i = βdag i := by
        by_contra hne
        apply hi
        unfold augSupport taskSupport
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      rw [if_pos hp, hβ]
      have t1 := abs_sub_le (βhat i) (b i) (βdag i)
      have t2 : |βdag i - b i| = |b i - βdag i| := abs_sub_comm _ _
      simp only [abs_zero]
      linarith
  have hfin := mul_le_mul_of_nonneg_left hcoord hlam
  nlinarith
