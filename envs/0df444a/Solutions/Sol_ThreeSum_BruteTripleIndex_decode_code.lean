-- Prove2me | solution 1 for ThreeSum.BruteTripleIndex.decode_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:09.217124+00:00
-- url     : https://prove2.me/submissions/32f65035-908d-492a-8d67-c939967744cb

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_BruteTripleIndex

set_option autoImplicit false
open ThreeSum ThreeSum.BruteTripleIndex
namespace ThreeSum.BruteTripleIndex
theorem _root_.solution {n : ℕ} (i j k : Fin n) :
    first n (code i j k)=i.val ∧ second n (code i j k)=j.val ∧ third n (code i j k)=k.val := by
  have hn : 0 < n := by have := i.isLt; omega
  have hq : code i j k/n=i.val*n+j.val := by
    unfold code
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt k.isLt]
    simp
  have hi : (i.val*n+j.val)/n=i.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt j.isLt]
    simp
  have hj : (i.val*n+j.val)%n=j.val := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]
  have hk : code i j k%n=k.val := by
    unfold code
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt k.isLt]
  exact ⟨by simp only [first,hq,hi],by simp only [second,hq,hj],hk⟩
end ThreeSum.BruteTripleIndex
