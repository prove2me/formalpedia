-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionPSL_conj_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:32:46.944612+00:00
-- url     : https://prove2.me/submissions/714cf0e7-bb8d-4aae-830f-96ad528d9001

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionPSL_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionPSL_conj_eq_inv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsEffectiveQuaternionPSL a t.conj (by simpa using ht) =
      (lpsEffectiveQuaternionPSL a t ht)⁻¹ := by
  simp only [lpsEffectiveQuaternionPSL_eq]
  exact lpsQuaternionPSL_conj_eq_inv a t ht
end QEC.Coding.TannerLiftedProduct
