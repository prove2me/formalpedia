-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P50.hermiticity_criteria
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:03:02.267476+00:00
-- url     : https://prove2.me/submissions/66b28020-5f62-4d3e-b316-217030b39ebc

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X6P50H

open QAlgorithms.Papers.Independent.Dependency50.P50

lemma preserves_iff {n m : ℕ}
    (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) :
    PreservesHermiticity T ↔ ∀ A : (Matrix (Fin n) (Fin n) ℂ), T (Aᴴ) = (T A)ᴴ := by
  constructor
  · intro h A
    set H : Matrix (Fin n) (Fin n) ℂ := (1/2 : ℂ) • (A + Aᴴ) with hH
    set K : Matrix (Fin n) (Fin n) ℂ := (-Complex.I/2 : ℂ) • (A - Aᴴ) with hK
    have hHh : H.IsHermitian := by
      unfold Matrix.IsHermitian
      rw [hH, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
      simp [add_comm]
    have hKh : K.IsHermitian := by
      unfold Matrix.IsHermitian
      rw [hK, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    have hA : A = H + Complex.I • K := by
      rw [hH, hK]; ext i j; simp [Complex.ext_iff]; constructor <;> ring
    have hAs : Aᴴ = H - Complex.I • K := by
      rw [hH, hK]; ext i j; simp [Complex.ext_iff]; constructor <;> ring
    have h1 := h H hHh
    have h2 := h K hKh
    unfold Matrix.IsHermitian at h1 h2
    clear_value H K
    rw [hAs, hA, map_sub, map_add, map_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, h1, h2]
    simp [sub_eq_add_neg]
  · intro h A hA
    unfold Matrix.IsHermitian at hA ⊢
    rw [← h, hA]

end X6P50H

open QAlgorithms.Papers.Independent.Dependency50.P50 X6P50H in
theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) {I : Type*} (E : Module.Basis I ℂ ((Matrix (Fin n) (Fin n) ℂ))) :
    (PreservesHermiticity T ↔ ∀ A : (Matrix (Fin n) (Fin n) ℂ), T (Aᴴ) = (T A)ᴴ) ∧
      (PreservesHermiticity T ↔ ∀ i : I, T ((E i)ᴴ) = (T (E i))ᴴ) := by
  refine ⟨preserves_iff T, ?_⟩
  rw [preserves_iff T]
  refine ⟨fun h i => h (E i), fun h => ?_⟩
  let f₁ : Matrix (Fin n) (Fin n) ℂ →ₛₗ[starRingEnd ℂ] Matrix (Fin m) (Fin m) ℂ :=
    T.comp (Matrix.conjTransposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap
  let f₂ : Matrix (Fin n) (Fin n) ℂ →ₛₗ[starRingEnd ℂ] Matrix (Fin m) (Fin m) ℂ :=
    (Matrix.conjTransposeLinearEquiv (Fin m) (Fin m) ℂ ℂ).toLinearMap.comp T
  have : f₁ = f₂ := E.ext fun i => h i
  intro A
  exact LinearMap.congr_fun this A
