-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.encode_digit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:36.92398+00:00
-- url     : https://prove2.me/submissions/36a0143a-aea1-4d2f-84c9-274e2bcbaa1d

import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f)
    (i : Fin f.natDegree) :
    encode hf x/p^i.val%p=((coefficients hf) x i).val := by
  let xs := List.ofFn fun j => ((coefficients hf) x j).val
  have hb : ∀ n∈xs, n<p := by
    intro n hn
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hn
    exact ZMod.val_lt _
  have hh : (xs.drop i.val).head?=some (((coefficients hf) x i).val) := by
    simp [xs,List.head?_drop,List.getElem?_ofFn,i.isLt]
  change Nat.ofDigits p xs/p^i.val%p=_
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i.val (Fact.out : p.Prime).pos xs hb,
    Nat.ofDigits_mod_eq_head!,List.head!_of_head? hh,Nat.mod_eq_of_lt (ZMod.val_lt _)]
end ThreeSum.TernaryExtensionEncoding
