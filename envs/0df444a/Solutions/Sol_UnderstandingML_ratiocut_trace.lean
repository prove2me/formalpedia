-- Prove2me | solution 1 for UnderstandingML.ratiocut_trace
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:46:33.357661+00:00
-- url     : https://prove2.me/submissions/6f339c48-da66-4f25-8dc1-507e0f71e7e6

import Definitions.Def_UnderstandingML_Clustering

open MeasureTheory

namespace UnderstandingML.RatioCutAux

/-- Quadratic form of the Laplacian on a scaled indicator vector:
`(a 𝟙_C)ᵀ L (a 𝟙_C) = a² ∑_{r ∈ C, s ∉ C} W_{r,s}` (no symmetry needed). -/
theorem laplacian_indicator {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (C : Finset (Fin m)) (a : ℝ) :
    ∑ s, (∑ r, (if r ∈ C then a else 0) * UnderstandingML.laplacian W r s) *
        (if s ∈ C then a else 0) =
      a ^ 2 * ∑ r ∈ C, ∑ s ∈ Cᶜ, W r s := by
  classical
  set h : Fin m → ℝ := fun r => if r ∈ C then a else 0 with hh
  show ∑ s, (∑ r, h r * UnderstandingML.laplacian W r s) * h s = a ^ 2 * ∑ r ∈ C, ∑ s ∈ Cᶜ, W r s
  have hinner : ∀ s, ∑ r, h r * UnderstandingML.laplacian W r s =
      h s * ∑ t, W s t - ∑ r, h r * W r s := by
    intro s
    simp only [UnderstandingML.laplacian, UnderstandingML.degreeMatrix, Matrix.sub_apply,
      Matrix.diagonal_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [hinner, sub_mul, Finset.sum_sub_distrib]
  have e1 : ∑ s, h s * (∑ t, W s t) * h s = a ^ 2 * ∑ r ∈ C, ∑ t, W r t := by
    have hterm : ∀ s, h s * (∑ t, W s t) * h s = if s ∈ C then a ^ 2 * ∑ t, W s t else 0 := by
      intro s
      simp only [hh]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.mul_sum]
  have e2 : ∑ s, (∑ r, h r * W r s) * h s = a ^ 2 * ∑ r ∈ C, ∑ s ∈ C, W r s := by
    have hterm : ∀ r s, h r * W r s * h s =
        if r ∈ C then (if s ∈ C then a ^ 2 * W r s else 0) else 0 := by
      intro r s
      simp only [hh]
      split_ifs <;> ring
    simp_rw [Finset.sum_mul, hterm]
    rw [Finset.sum_comm]
    simp_rw [← Finset.ite_sum_zero, Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  rw [e1, e2, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_add_sum_compl C (fun t => W r t)]
  ring

end UnderstandingML.RatioCutAux

open UnderstandingML.RatioCutAux in
theorem solution {m k : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (hW : W.IsSymm)
    (C : Fin k → Finset (Fin m)) (hC : UnderstandingML.IsPartition Finset.univ C)
    (hne : ∀ i, (C i).Nonempty) :
    (UnderstandingML.clusterIndicator C).transpose * UnderstandingML.clusterIndicator C = 1 ∧
      UnderstandingML.ratioCut W C = Matrix.trace ((UnderstandingML.clusterIndicator C).transpose *
        UnderstandingML.laplacian W * UnderstandingML.clusterIndicator C) := by
  classical
  have hsq : ∀ j, (1 / Real.sqrt ((C j).card)) ^ 2 = ((C j).card : ℝ)⁻¹ := by
    intro j
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _), one_div]
  constructor
  · ext j j'
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, UnderstandingML.clusterIndicator]
    by_cases hjj : j = j'
    · subst hjj
      simp only [Matrix.one_apply_eq, mul_ite, ite_mul, mul_zero, zero_mul]
      have hterm : ∀ x, (if x ∈ C j then (if x ∈ C j then
          1 / Real.sqrt ((C j).card) * (1 / Real.sqrt ((C j).card)) else 0) else 0) =
          if x ∈ C j then ((C j).card : ℝ)⁻¹ else 0 := by
        intro x
        split_ifs
        · rw [← hsq j, sq]
        · rfl
      rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
      have hcard : ((C j).card : ℝ) ≠ 0 := by exact_mod_cast (hne j).card_pos.ne'
      field_simp
    · rw [Matrix.one_apply_ne hjj]
      refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with h1 h2
      · exact absurd ((hC.2 x (Finset.mem_univ x)).unique h1 h2) hjj
      all_goals simp
  · unfold UnderstandingML.ratioCut
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    have := laplacian_indicator W (C j) (1 / Real.sqrt ((C j).card))
    simp only [UnderstandingML.clusterIndicator]
    rw [this, hsq]
