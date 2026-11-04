-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.remainderRelation_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:20.047327+00:00
-- url     : https://prove2.me/submissions/9b47bba6-c9e4-4115-908d-57314dd80415

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_coefficients_mk_vector

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic)
    (a b h r : Fin f.natDegree → ZMod p) (hr : remainderRelation a b h r) :
    coefficients hf ((coefficients hf).symm a*(coefficients hf).symm b)=r := by
  have ha : (coefficients hf).symm a=AdjoinRoot.mk f (vectorPolynomial a) :=
    (LinearEquiv.symm_apply_eq (coefficients hf)).mpr (coefficients_mk_vector hf a).symm
  have hb : (coefficients hf).symm b=AdjoinRoot.mk f (vectorPolynomial b) :=
    (LinearEquiv.symm_apply_eq (coefficients hf)).mpr (coefficients_mk_vector hf b).symm
  rw [ha,hb,← map_mul]
  change vectorPolynomial a*vectorPolynomial b=vectorPolynomial h*f+vectorPolynomial r at hr
  rw [hr,map_add,map_mul,AdjoinRoot.mk_self,mul_zero,zero_add]
  exact coefficients_mk_vector hf r
end ThreeSum.TernaryExtensionEncoding
