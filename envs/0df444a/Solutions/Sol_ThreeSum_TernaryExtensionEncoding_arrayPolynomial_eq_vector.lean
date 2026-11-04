-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.arrayPolynomial_eq_vector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:17.179065+00:00
-- url     : https://prove2.me/submissions/a97a49c5-38db-436a-997b-7af3a8c8532e

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d : ℕ} (a : Fin d → ZMod p) :
    arrayPolynomial d (fun i => if h : i<d then (a ⟨i,h⟩).val else 0)=
      vectorPolynomial a := by
  unfold arrayPolynomial vectorPolynomial
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  simp [i.isLt]
end ThreeSum.TernaryExtensionEncoding
