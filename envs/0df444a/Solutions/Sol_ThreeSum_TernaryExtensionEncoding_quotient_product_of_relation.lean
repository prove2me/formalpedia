-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.quotient_product_of_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:55.559286+00:00
-- url     : https://prove2.me/submissions/bc16b3bb-0128-467d-b73c-82292e7deda4

import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_remainderRelation_correct


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic)
    (x y : AdjoinRoot f) (h r : Fin f.natDegree → ZMod p)
    (hr : remainderRelation (coefficients hf x) (coefficients hf y) h r) :
    coefficients hf (x*y)=r := by
  simpa only [LinearEquiv.symm_apply_apply] using
    remainderRelation_correct hf (coefficients hf x) (coefficients hf y) h r hr
end ThreeSum.TernaryExtensionEncoding
