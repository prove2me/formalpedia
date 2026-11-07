-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionPSL_conj_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:36:44.040221+00:00
-- url     : https://prove2.me/submissions/51672fd7-7274-4556-85c9-d245ca128c4d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_toPGL_lpsQuaternionPSL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionPGL_conj_eq_inv
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
    lpsQuaternionPSL a t.conj (by simpa using ht) =
      (lpsQuaternionPSL a t ht)⁻¹ := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [map_inv, toPGL_lpsQuaternionPSL, toPGL_lpsQuaternionPSL]
  exact lpsQuaternionPGL_conj_eq_inv a t ht
end QEC.Coding.TannerLiftedProduct
