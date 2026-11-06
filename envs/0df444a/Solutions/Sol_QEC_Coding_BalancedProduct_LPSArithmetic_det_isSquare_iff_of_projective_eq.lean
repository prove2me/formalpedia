-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSArithmetic.det_isSquare_iff_of_projective_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:49:00.666201+00:00
-- url     : https://prove2.me/submissions/df504efe-ada8-4650-8d92-ce20c2e240cd

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]
namespace QEC.Coding.BalancedProduct.LPSArithmetic
theorem _root_.solution
    {A B : GL (Fin 2) R}
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    IsSquare A.det ↔ IsSquare B.det := by
  change QuotientGroup.mk' (Subgroup.center (GL (Fin 2) R)) A =
      QuotientGroup.mk' (Subgroup.center (GL (Fin 2) R)) B at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨z, hz, hAz⟩
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  rcases hz with ⟨u, rfl⟩
  have hdet := congrArg Matrix.GeneralLinearGroup.det hAz
  simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin] at hdet
  constructor
  · intro hA
    rw [← hdet]
    exact hA.mul (IsSquare.sq u)
  · intro hB
    have hBinv : IsSquare (B.det * (u⁻¹ ^ 2)) :=
      hB.mul (IsSquare.sq u⁻¹)
    convert hBinv using 1
    calc
      A.det = A.det * (u ^ 2 * u⁻¹ ^ 2) := by simp
      _ = (A.det * u ^ 2) * u⁻¹ ^ 2 := by ac_rfl
      _ = B.det * u⁻¹ ^ 2 := by rw [hdet]
end QEC.Coding.BalancedProduct.LPSArithmetic
