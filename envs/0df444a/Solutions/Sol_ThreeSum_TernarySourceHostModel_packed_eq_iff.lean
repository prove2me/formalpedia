-- Prove2me | solution 1 for ThreeSum.TernarySourceHostModel.packed_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:27:19.884196+00:00
-- url     : https://prove2.me/submissions/35dd6b79-d75c-472f-a066-3b2d2d4ef248

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
theorem _root_.solution (bank g h a b : ℕ) (ha : a<bank) (hb : b<bank) :
    g*bank+a=h*bank+b ↔ g=h ∧ a=b := by
  have hbank : 0<bank := by omega
  have hdiv (g a : ℕ) (ha : a<bank) : (g*bank+a)/bank=g := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hbank,Nat.div_eq_of_lt ha,Nat.zero_add]
  constructor
  · intro he
    have hg := congrArg (fun z => z/bank) he
    rw [hdiv g a ha,hdiv h b hb] at hg
    rw [hg] at he
    exact ⟨hg,by omega⟩
  · rintro ⟨rfl,rfl⟩; rfl
end ThreeSum.TernarySourceHostModel
