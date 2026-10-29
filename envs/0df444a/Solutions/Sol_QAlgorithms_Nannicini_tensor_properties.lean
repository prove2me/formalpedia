-- Prove2me | solution 1 for QAlgorithms.Nannicini.tensor_properties
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-10-29T00:43:15.593217+00:00
-- url     : https://prove2.me/submissions/d9d9207e-e6c0-4cf2-848d-7ddfd2497b44

import Definitions.Def_QAlgorithms_Defs_Measurement
set_option autoImplicit false

open QAlgorithms in
theorem solution {m n : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (C D : Matrix (Fin n) (Fin n) ℂ) (u v : EuclideanSpace ℂ (Fin m))
    (w x : EuclideanSpace ℂ (Fin n)) (a b : ℂ) :
    Matrix.kronecker A C * Matrix.kronecker B D = Matrix.kronecker (A * B) (C * D) ∧
    act (Matrix.kronecker A C) (tensorVec u w) = tensorVec (act A u) (act C w) ∧
    tensorVec (u + v) w = tensorVec u w + tensorVec v w ∧
    tensorVec u (w + x) = tensorVec u w + tensorVec u x ∧
    tensorVec (a • u) (b • w) = (a * b) • tensorVec u w ∧
    (Matrix.kronecker A C).conjTranspose =
      Matrix.kronecker A.conjTranspose C.conjTranspose := by
  refine ⟨(Matrix.mul_kronecker_mul A B C D).symm, ?_, ?_, ?_, ?_,
    Matrix.conjTranspose_kronecker A C⟩
  · apply PiLp.ext
    rintro ⟨i, k⟩
    change (∑ jl : Fin m × Fin n,
      (A i jl.1 * C k jl.2) * (u jl.1 * w jl.2)) =
      (∑ j : Fin m, A i j * u j) * (∑ l : Fin n, C k l * w l)
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  · apply PiLp.ext
    rintro ⟨i, j⟩
    change (u i + v i) * w j = u i * w j + v i * w j
    ring
  · apply PiLp.ext
    rintro ⟨i, j⟩
    change u i * (w j + x j) = u i * w j + u i * x j
    ring
  · apply PiLp.ext
    rintro ⟨i, j⟩
    change (a * u i) * (b * w j) = (a * b) * (u i * w j)
    ring

#print axioms solution
