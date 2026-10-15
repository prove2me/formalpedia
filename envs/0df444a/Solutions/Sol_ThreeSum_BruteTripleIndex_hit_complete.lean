-- Prove2me | solution 1 for ThreeSum.BruteTripleIndex.hit_complete
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:42:26.905879+00:00
-- url     : https://prove2.me/submissions/9fc48294-4092-4bab-b405-a41a6e3042d2

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-! # A literal order of all original-position triples for the finite fallback -/

namespace ThreeSum.BruteTripleIndex













theorem code_lt {n : ℕ} (i j k : Fin n) : code i j k < n^3 := by
  have hpair : i.val*n+j.val < n*n := by
    calc
      _ < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by ring
      _ ≤ n*n := Nat.mul_le_mul_right n (by omega)
  calc
    code i j k < (i.val*n+j.val)*n+n := Nat.add_lt_add_left k.isLt _
    _ = (i.val*n+j.val+1)*n := by ring
    _ ≤ (n*n)*n := Nat.mul_le_mul_right n (by omega)
    _ = n^3 := by ring

theorem decode_code {n : ℕ} (i j k : Fin n) :
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


























theorem hit_complete_sourceProof {n : ℕ} (x : Fin n → ℤ) (hn : 0 < n) :
    Hit x hn (n^3) ↔ Coloring.DistinctZeroSum x := by
  constructor
  · rintro ⟨i,hi,_,hx⟩
    exact ⟨⟨first n i,(bounds hn hi).1⟩,⟨second n i,(bounds hn hi).2.1⟩,
      ⟨third n i,(bounds hn hi).2.2⟩,hx⟩
  · rintro ⟨i,j,k,hij,hik,hjk,hzero⟩
    refine ⟨code i j k,code_lt i j k,code_lt i j k,?_⟩
    have ha : (⟨first n (code i j k),(bounds hn (code_lt i j k)).1⟩ : Fin n)=i :=
      Fin.ext (decode_code i j k).1
    have hb : (⟨second n (code i j k),(bounds hn (code_lt i j k)).2.1⟩ : Fin n)=j :=
      Fin.ext (decode_code i j k).2.1
    have hc : (⟨third n (code i j k),(bounds hn (code_lt i j k)).2.2⟩ : Fin n)=k :=
      Fin.ext (decode_code i j k).2.2
    simpa only [witness,ha,hb,hc] using And.intro hij (And.intro hik (And.intro hjk hzero))

end ThreeSum.BruteTripleIndex

end


theorem solution : ∀ {n : Nat} (x : Fin n → Int)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
  Iff
    (@ThreeSum.BruteTripleIndex.Hit n x hn
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@ThreeSum.Coloring.DistinctZeroSum n x) := by
  exact @ThreeSum.BruteTripleIndex.hit_complete_sourceProof

#print axioms solution
