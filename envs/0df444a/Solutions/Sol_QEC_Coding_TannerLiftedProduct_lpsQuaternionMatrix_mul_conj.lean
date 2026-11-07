-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionMatrix_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:34:26.440722+00:00
-- url     : https://prove2.me/submissions/fa735fd7-c9c4-43f9-b06a-4f0868a4d5aa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionMatrix_conj

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open QEC.Coding.BalancedProduct.LPSArithmetic
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q : ℕ) [Fact q.Prime] (t : LPSQuaternion) :
    lpsQuaternionMatrix q t * lpsQuaternionMatrix q t.conj =
      (t.norm : ZMod q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  rw [lpsQuaternionMatrix_conj, Matrix.mul_adjugate,
    det_lpsQuaternionMatrix]
end QEC.Coding.TannerLiftedProduct
