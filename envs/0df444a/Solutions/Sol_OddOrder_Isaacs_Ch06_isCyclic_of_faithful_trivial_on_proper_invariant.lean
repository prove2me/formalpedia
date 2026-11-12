-- Prove2me | solution 1 for OddOrder.Isaacs.Ch06.isCyclic_of_faithful_trivial_on_proper_invariant
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:34:55.836055+00:00
-- url     : https://prove2.me/submissions/9d0b17db-d785-44cd-b5ca-3c4b43adfaa6

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

section

universe uA uN

/-- **Isaacs Lem 6.20**: if a finite abelian group acts faithfully and coprimely on `N`,
and acts trivially on every proper invariant subgroup of `N`, then it is cyclic. -/
theorem _root_.solution
    {A : Type uA} {N : Type uN} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [MulDistribMulAction A N] [FaithfulSMul A N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N))
    (hproper :
      ∀ M : Subgroup N,
        (∀ a : A, ∀ n ∈ M, a • n ∈ M) →
        M ≠ ⊤ →
        ∀ a : A, ∀ n ∈ M, a • n = n) :
    IsCyclic A := by
  classical
  by_contra hNotCyclic
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let fixedTop : Subgroup N := actionFixedPoints φ ⊤
  have hKtop : nontrivialActionFixedByClosure φ = ⊤ :=
    nontrivialActionFixedByClosure_eq_top_of_not_isCyclic hCop hNotCyclic
  have hK_le_fixedTop : nontrivialActionFixedByClosure φ ≤ fixedTop := by
    rw [nontrivialActionFixedByClosure_le_iff]
    intro a ha
    let M : Subgroup N := actionFixedBy φ a
    have hM_inv : ∀ b : A, ∀ n ∈ M, b • n ∈ M := by
      intro b n hn
      have hmem :
          (φ b) n ∈ actionFixedBy φ a :=
        actionFixedBy_invariant_of_commute (φ := φ) (a := a) (b := b)
          (mul_comm a b) n hn
      simpa [φ, M] using hmem
    have hM_ne_top : M ≠ ⊤ := by
      intro hMtop
      have ha_one : a = 1 := by
        exact eq_of_smul_eq_smul fun n : N => by
          have hn : n ∈ M := by
            rw [hMtop]
            exact Subgroup.mem_top n
          change (φ a) n = n at hn
          simpa [φ] using hn
      exact ha ha_one
    have hM_trivial := hproper M hM_inv hM_ne_top
    intro n hn
    change ∀ b : (⊤ : Subgroup A), (φ b) n = n
    intro b
    have hfix := hM_trivial (b : A) n hn
    simpa [φ] using hfix
  have hfixedTop_eq_top : fixedTop = ⊤ := by
    rw [eq_top_iff]
    intro n _hn
    exact hK_le_fixedTop (by
      rw [hKtop]
      exact Subgroup.mem_top n)
  have hA_subsingleton : Subsingleton A := by
    refine ⟨fun a b => ?_⟩
    have ha : a = 1 := by
      exact eq_of_smul_eq_smul fun n : N => by
        have hn : n ∈ fixedTop := by
          rw [hfixedTop_eq_top]
          exact Subgroup.mem_top n
        have hfix := hn ⟨a, Subgroup.mem_top a⟩
        change (φ a) n = n at hfix
        simpa [φ] using hfix
    have hb : b = 1 := by
      exact eq_of_smul_eq_smul fun n : N => by
        have hn : n ∈ fixedTop := by
          rw [hfixedTop_eq_top]
          exact Subgroup.mem_top n
        have hfix := hn ⟨b, Subgroup.mem_top b⟩
        change (φ b) n = n at hfix
        simpa [φ] using hfix
    exact ha.trans hb.symm
  exact hNotCyclic (@isCyclic_of_subsingleton A _ hA_subsingleton)

end

end OddOrder.Isaacs.Ch06
