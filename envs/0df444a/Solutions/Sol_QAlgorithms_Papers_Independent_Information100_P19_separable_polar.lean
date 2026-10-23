-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.separable_polar
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T12:52:11.960074+00:00
-- url     : https://prove2.me/submissions/87616add-4fc2-4d48-a7c6-072114ff935f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

set_option autoImplicit false

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (n : ℕ) (hn : 1 ≤ n) : sepCone n = tensorPolar (sepMom n) := by
  ext f
  constructor
  · intro hf y hy
    have hclosed : IsClosed {y : Perms n → ℝ | 0 ≤ ∑ p, f p * y p} :=
      isClosed_le continuous_const
        (continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_apply p))
    have hsub : finiteCone {y : Perms n → ℝ | ∃ a b, 0 < a ∧ 0 < b ∧ ∃ X : Bip a b,
        QAlgorithms.Entanglement.IsSeparablePositive X ∧ y = fun p => (tensorTrace p X).re}
        ⊆ {y : Perms n → ℝ | 0 ≤ ∑ p, f p * y p} := by
      rintro v ⟨N, c, u, hu, rfl⟩
      have key : ∑ p, f p * (∑ i, c i • u i) p = ∑ i, c i * ∑ p, f p * u i p := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
      show 0 ≤ ∑ p, f p * (∑ i, c i • u i) p
      rw [key]
      refine Finset.sum_nonneg fun i _ => mul_nonneg (hu i).1 ?_
      obtain ⟨a, b, ha, hb, X, hX, hy⟩ := (hu i).2
      rw [hy]
      exact hf a b ha hb X hX
    exact closure_minimal hsub hclosed hy
  · intro hf a b ha hb X hX
    have hy : (fun p => (tensorTrace p X).re) ∈ sepMom n := by
      apply subset_closure
      refine ⟨1, fun _ => 1, fun _ => fun p => (tensorTrace p X).re,
        fun _ => ⟨zero_le_one, a, b, ha, hb, X, hX, rfl⟩, ?_⟩
      simp
    exact hf _ hy
