-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.remainderRelation_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:54.136224+00:00
-- url     : https://prove2.me/submissions/e31c49ef-7551-417b-a2ee-26cb4aa804ef

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_vectorPolynomial_of_natDegree_lt
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_vectorPolynomial_degree_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) (a b : Fin f.natDegree → ZMod p) :
    ∃ h r : Fin f.natDegree → ZMod p, remainderRelation a b h r := by
  let z := vectorPolynomial a*vectorPolynomial b
  have hv (c : Fin f.natDegree → ZMod p) : (vectorPolynomial c).natDegree<f.natDegree := by
    by_cases hz : vectorPolynomial c=0
    · simpa only [hz,natDegree_zero] using hd
    · exact (natDegree_lt_iff_degree_lt hz).mpr (vectorPolynomial_degree_lt c)
  have ha := hv a
  have hb := hv b
  have hz : z.natDegree<2*f.natDegree := by
    exact (natDegree_mul_le.trans_lt (by omega))
  have hq : (z /ₘ f).natDegree<f.natDegree := by rw [natDegree_divByMonic z hf]; omega
  have hf1 : f≠1 := by intro h; rw [h,natDegree_one] at hd; omega
  have hrem := natDegree_modByMonic_lt z hf hf1
  refine ⟨fun i => (z /ₘ f).coeff i.val,fun i => (z %ₘ f).coeff i.val,?_⟩
  unfold remainderRelation
  rw [vectorPolynomial_of_natDegree_lt hq,vectorPolynomial_of_natDegree_lt hrem]
  change z=(z /ₘ f)*f+z %ₘ f
  rw [add_comm,mul_comm]
  exact (modByMonic_add_div z f).symm
end ThreeSum.TernaryExtensionEncoding
