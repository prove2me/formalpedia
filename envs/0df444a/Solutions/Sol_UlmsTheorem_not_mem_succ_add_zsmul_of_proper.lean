-- Prove2me | solution 1 for UlmsTheorem.not_mem_succ_add_zsmul_of_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:30.175377+00:00
-- url     : https://prove2.me/submissions/59a8cae8-a72f-4970-9a5f-186490b2faf9

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Theorems.Thm_UlmsTheorem_isProper_iff_forall_not_mem_succ
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution
    {A : AddSubgroup G} {x : G} {α : Ordinal.{0}}
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p A x)
    (hpxA : p • x ∈ A)
    (a : A) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) :
    (a : G) + n • x ∉ ulmSubgroup p (Order.succ α) (G := G) := by
  intro hz
  have hcop_nat : Nat.Coprime p n.natAbs := by
    refine (Nat.Prime.coprime_iff_not_dvd Fact.out).2 ?_
    intro hdiv
    exact hn (Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 hdiv))
  have hcop : n.gcd ↑p = 1 := by
    rw [Int.gcd_eq_natAbs]
    simpa [Nat.gcd_comm] using hcop_nat.gcd_eq_one
  have hbez : (1 : ℤ) = n * n.gcdA ↑p + ↑p * n.gcdB ↑p := by
    simpa [hcop] using (Int.gcd_eq_gcd_ab n p)
  let pxA : A := ⟨(p : ℤ) • x, by simpa using hpxA⟩
  let s : A :=
    n.gcdA ↑p • a - n.gcdB ↑p • pxA
  have hxs :
      x + (s : G) = n.gcdA ↑p • ((a : G) + n • x) := by
    change x + (n.gcdA ↑p • (a : G) - n.gcdB ↑p • ((p : ℤ) • x)) =
      n.gcdA ↑p • ((a : G) + n • x)
    rw [smul_add, ← mul_zsmul, ← mul_zsmul]
    have hcoeff :
        (1 : ℤ) - n.gcdB ↑p * p = n.gcdA ↑p * n := by
      have hbez' :
          (1 : ℤ) = n.gcdA ↑p * n + n.gcdB ↑p * p := by
        simpa [Int.mul_comm] using hbez
      omega
    calc
      x + (n.gcdA ↑p • (a : G) - (n.gcdB ↑p * p) • x) =
          n.gcdA ↑p • (a : G) +
            ((1 : ℤ) - n.gcdB ↑p * p) • x := by
              rw [sub_zsmul, one_zsmul]
              abel
      _ = n.gcdA ↑p • (a : G) + (n.gcdA ↑p * n) • x := by
            rw [hcoeff]
  have hxsSucc : x + (s : G) ∈
      ulmSubgroup p (Order.succ α) (G := G) := by
    rw [hxs]
    exact (ulmSubgroup p (Order.succ α)).zsmul_mem hz _
  exact (isProper_iff_forall_not_mem_succ p _ hxα hxSucc).1 hxProper s hxsSucc
end UlmsTheorem
