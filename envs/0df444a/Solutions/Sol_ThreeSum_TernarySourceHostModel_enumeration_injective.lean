-- Prove2me | solution 1 for ThreeSum.TernarySourceHostModel.enumeration_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:54.826357+00:00
-- url     : https://prove2.me/submissions/5bd896e5-c7e5-4dd6-b407-c48aa7a8fddc

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceHostModel
open Finset Light TernaryJointType
open scoped BigOperators
variable {N : ℕ}
namespace ThreeSum.TernarySourceHostModel
theorem _root_.solution (enumeration : ℕ → TritWord N) (bank : ℕ)
    (hsorted : ∀ i j, i<j → j<bank →
      TernaryCodeSemantics.address (enumeration i)<TernaryCodeSemantics.address (enumeration j)) :
    ∀ i j, i<bank → j<bank → enumeration i=enumeration j → i=j := by
  intro i j hi hj he
  rcases lt_trichotomy i j with hij|hij|hij
  · have hh := hsorted i j hij hj
    rw [he] at hh
    omega
  · exact hij
  · have hh := hsorted j i hij hi
    rw [he] at hh
    omega
end ThreeSum.TernarySourceHostModel
