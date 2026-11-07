-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionPGL_conj_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:35:43.50918+00:00
-- url     : https://prove2.me/submissions/8d30b408-7fbe-4f45-99cc-160912a30d2a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionMatrix_mul_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open QEC.Coding.BalancedProduct.LPSArithmetic
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsQuaternionPGL a t.conj (by simpa using ht) =
      (lpsQuaternionPGL a t ht)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  change Matrix.ProjGenLinGroup.mk (lpsQuaternionGL a t ht) *
      Matrix.ProjGenLinGroup.mk
        (lpsQuaternionGL a t.conj (by simpa using ht)) = 1
  rw [← map_mul]
  apply (Matrix.ProjGenLinGroup.mk_eq_one).mpr
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨(lpsQuaternionGL a t ht).det, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hnorm : (t.norm : ZMod a.q) = (p : ZMod a.q) := by
    rw [ht]
    norm_cast
  have hmatrix :
      Matrix.scalar (Fin 2) ((lpsQuaternionGL a t ht).det : ZMod a.q) =
        lpsQuaternionMatrix a.q t * lpsQuaternionMatrix a.q t.conj := by
    rw [lpsQuaternionGL_det a t ht]
    calc
      Matrix.scalar (Fin 2) (p : ZMod a.q) =
          (p : ZMod a.q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod a.q)) := by
        change Matrix.diagonal (fun _ : Fin 2 => (p : ZMod a.q)) =
          (p : ZMod a.q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod a.q))
        exact (Matrix.smul_one_eq_diagonal (p : ZMod a.q)).symm
      _ = (t.norm : ZMod a.q) •
          (1 : Matrix (Fin 2) (Fin 2) (ZMod a.q)) := by rw [hnorm]
      _ = lpsQuaternionMatrix a.q t *
          lpsQuaternionMatrix a.q t.conj :=
        (lpsQuaternionMatrix_mul_conj a.q t).symm
  exact congrFun (congrFun hmatrix i) j
end QEC.Coding.TannerLiftedProduct
