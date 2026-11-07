-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsQuaternionGeneratorsPSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:36:28.486927+00:00
-- url     : https://prove2.me/submissions/5481521b-01ba-4a1f-838c-b82be1ad4155

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionPSL_injective

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) :
    (lpsQuaternionGeneratorsPSL a).card =
      (lpsQuaternionShell p).card := by
  classical
  rw [lpsQuaternionGeneratorsPSL,
    Finset.card_image_of_injective _ (lpsQuaternionPSL_injective a),
    Finset.card_attach]
end QEC.Coding.TannerLiftedProduct
