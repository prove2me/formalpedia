-- Prove2me | solution 1 for QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.exists_algHom_matrix_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0bbb56c4-5d19-5b44-a92b-9cdbc5955767

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_algHom_matrix_injective

set_option autoImplicit false

open scoped MatrixGroups Quaternion
open QuaternionAlgebra CerednikDrinfeld

namespace RealSplit10

noncomputable def D (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![s, 0; 0, -s]
noncomputable def J (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; c, 0]

theorem D_mul_D (s : ℝ) : D s * D s = (s * s) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D, Matrix.mul_apply, Fin.sum_univ_two]
theorem J_mul_J (c : ℝ) : J c * J c = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]
theorem J_mul_D (s c : ℝ) : J c * D s = -(D s * J c) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D, J, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem ratSmul_eq (r : ℚ) (M : Matrix (Fin 2) (Fin 2) ℝ) : r • M = (r : ℝ) • M := by
  rw [← algebraMap_smul ℝ r M]; rfl

noncomputable def basisA (a b : ℚ) (ha : 0 ≤ a) : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℝ) a 0 b where
  i := D (Real.sqrt a)
  j := J b
  k := D (Real.sqrt a) * J b
  i_mul_i := by
    rw [D_mul_D, Real.mul_self_sqrt (by exact_mod_cast ha), zero_smul, add_zero, ratSmul_eq]
  j_mul_j := by rw [J_mul_J, ratSmul_eq]
  i_mul_j := rfl
  j_mul_i := by rw [J_mul_D, zero_smul, zero_sub]

noncomputable def basisB (a b : ℚ) (hb : 0 ≤ b) : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℝ) a 0 b where
  i := J a
  j := D (Real.sqrt b)
  k := J a * D (Real.sqrt b)
  i_mul_i := by rw [J_mul_J, zero_smul, add_zero, ratSmul_eq]
  j_mul_j := by rw [D_mul_D, Real.mul_self_sqrt (by exact_mod_cast hb), ratSmul_eq]
  i_mul_j := rfl
  j_mul_i := by rw [J_mul_D, zero_smul, zero_sub, neg_neg]

end RealSplit10

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q') :
    ∃ ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ, Function.Injective ι := by

  have hex : ∃ ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ, True := by
    rcases hB.1 with ha | hb
    · exact ⟨(RealSplit10.basisA a b ha.le).liftHom, trivial⟩
    · exact ⟨(RealSplit10.basisB a b hb.le).liftHom, trivial⟩
  obtain ⟨ι, -⟩ := hex
  refine ⟨ι, ?_⟩

  intro x y hxy
  by_contra hne
  have hu : IsUnit (x - y) := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB _ (sub_ne_zero.2 hne)
  have h0 : ι (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact (hu.map ι).ne_zero h0

end S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_algHom_matrix_injective
end P2MW
export P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_exists_algHom_matrix_injective (solution)
