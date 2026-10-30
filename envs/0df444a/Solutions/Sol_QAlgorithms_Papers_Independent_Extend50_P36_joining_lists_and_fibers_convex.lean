-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P36.joining_lists_and_fibers_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:06:27.080924+00:00
-- url     : https://prove2.me/submissions/9558b1d5-a087-4116-9500-b878c771b656

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ComplexOrder
open QAlgorithms.Papers.Independent.Extend50.P36
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem s110_jl_marg {N : ℕ} (dim : Fin N → ℕ) (S : Finset (Fin N))
    (X Y : Op ((i : Fin N) → Fin (dim i))) (a b : ℝ) :
    neighborhoodMarginal dim S (a • X + b • Y) =
      a • neighborhoodMarginal dim S X + b • neighborhoodMarginal dim S Y := by
  ext u v
  simp only [neighborhoodMarginal, Matrix.add_apply, Matrix.smul_apply, Finset.sum_add_distrib,
    Finset.smul_sum]

theorem s110_jl_dens {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ)
    (hX : QAlgorithms.IsDensityMatrix X) (hY : QAlgorithms.IsDensityMatrix Y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    QAlgorithms.IsDensityMatrix (a • X + b • Y) := by
  refine ⟨(hX.1.smul ha).add (hY.1.smul hb), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX.2, hY.2, ← add_smul, hab, one_smul]

theorem solution (N q : ℕ) (dim : Fin N → ℕ)
    (hdim : ∀ i, 0 < dim i) (S : Fin q → Finset (Fin N)) :
    Convex ℝ {rho : (j : Fin q) → Op (NeighborhoodConfiguration dim (S j)) | ∃ X, JoiningList dim S rho X} ∧
    (∀ rho : (j : Fin q) → Op (NeighborhoodConfiguration dim (S j)),
      Convex ℝ {X | JoiningList dim S rho X}) := by
  constructor
  · rintro r1 ⟨X1, hX1, hm1⟩ r2 ⟨X2, hX2, hm2⟩ a b ha hb hab
    refine ⟨a • X1 + b • X2, s110_jl_dens X1 X2 hX1 hX2 a b ha hb hab, fun j => ?_⟩
    rw [s110_jl_marg, hm1, hm2]
    rfl
  · intro rho X1 ⟨hX1, hm1⟩ X2 ⟨hX2, hm2⟩ a b ha hb hab
    refine ⟨s110_jl_dens X1 X2 hX1 hX2 a b ha hb hab, fun j => ?_⟩
    rw [s110_jl_marg, hm1, hm2, ← add_smul, hab, one_smul]
