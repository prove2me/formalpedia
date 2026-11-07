-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.toPGL_lpsEffectiveQuaternionPSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:54:26.023126+00:00
-- url     : https://prove2.me/submissions/0e94f729-7450-4fb4-b7fe-d0288404a1cb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (lpsEffectiveQuaternionPSL a t ht) =
      lpsQuaternionPGL a t ht := by
  change Matrix.ProjGenLinGroup.mk
    (Matrix.SpecialLinearGroup.toGL (lpsEffectiveQuaternionSL a t ht)) =
      Matrix.ProjGenLinGroup.mk (lpsQuaternionGL a t ht)
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 (lpsEffectiveDegreeRoot a) (lpsEffectiveDegreeRoot_ne_zero a), ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpsEffectiveQuaternionSL, lpsQuaternionGL, Matrix.SpecialLinearGroup.toGL,
      Matrix.mul_apply, mul_comm, mul_assoc, lpsEffectiveDegreeRoot_ne_zero a]
end QEC.Coding.TannerLiftedProduct
