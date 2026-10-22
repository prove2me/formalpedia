-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.choi_basis_change
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:17:14.545365+00:00
-- url     : https://prove2.me/submissions/53083413-2b30-4070-85fc-26c4647ce83b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P23
open QAlgorithms

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

theorem solution (din dout : ℕ)
    (Phi : Op (Fin din) →ₗ[ℂ] Op (Fin dout)) (V : Op (Fin din)) (W : Op (Fin dout)) :
    functionOutputChoi (fun rho => Wᴴ * Phi (V * rho * Vᴴ) * W) =
      (Matrix.kronecker W (fun i j => conj (V i j)))ᴴ * functionOutputChoi Phi *
        Matrix.kronecker W (fun i j => conj (V i j)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  have hV : V * Matrix.single i j 1 * Vᴴ =
      ∑ i' : Fin din, ∑ j' : Fin din, (V i' i * conj (V j' j)) • Matrix.single i' j' (1 : ℂ) := by
    ext x y
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, Matrix.conjTranspose_apply, ite_and,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_mul]
  show (Wᴴ * Phi (V * Matrix.single i j 1 * Vᴴ) * W) a b = _
  rw [hV]
  simp only [map_sum, map_smul]
  simp only [functionOutputChoi, QAlgorithms.Papers.Independent.Information100.P34.choi,
    Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, smul_eq_mul,
    star_mul', Complex.star_def, Complex.conj_conj]
  simp only [Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, map_mul, Complex.conj_conj]
  have e1 : ∀ (G : Fin din → Fin din → Fin dout → ℂ),
      ∑ y, ∑ x, ∑ x_1, G y x x_1 = ∑ x, ∑ x_1, ∑ y, G y x x_1 := by
    intro G
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [e1]
  refine Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun i' _ => ?_
  ring

end
