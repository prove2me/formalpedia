-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.lambda_tau1_apply_eq_of_not_mem_H_sat_core
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:56:43.058864+00:00
-- url     : https://prove2.me/submissions/ab47d8c4-b112-4a38-bd3e-c96736781a3b

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/TISubsetCounting.lean
--   OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

-- ===== OddOrder/GroupTheory/TISubsetCounting.lean =====
namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

namespace IsTISubset

open scoped Pointwise

/-- **Induced value off the TI-saturation**: an `A`-supported class function of `L` induces to
a function vanishing off the conjugacy saturation `A^G` — every induction summand lands
outside the support. -/
theorem induce_apply_of_not_mem_conjClassSet {k : Type*} [Field k] [Fintype G]
    {A : Set G} {L : Subgroup G} [Invertible (Nat.card ↥L : k)]
    (α : OddOrder.RepresentationTheory.ClassFunction ↥L k)
    (hsupp : ∀ w : ↥L, (w : G) ∉ A → α w = 0)
    {g : G} (hg : g ∉ conjClassSet A) :
    OddOrder.RepresentationTheory.ClassFunction.induce L α g = 0 := by
  classical
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply]
  have hterm : ∀ x : G, OddOrder.RepresentationTheory.ClassFunction.induceTerm L α x g = 0 := by
    intro x
    by_cases hmemL : x⁻¹ * g * x ∈ L
    · rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_mem α hmemL]
      refine hsupp _ (fun hmemA => hg ?_)
      rw [mem_conjClassSet]
      exact ⟨x⁻¹ * g * x, hmemA, x, by group⟩
    · exact OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_not_mem α hmemL
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const_zero, mul_zero]

end IsTISubset

end OddOrder.GroupTheory

-- ===== OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The `λ^{τ₁}`-value off the `H^#`-saturation is `±` an `η`-column sum** (Peterfalvi
(13.9.a) first step — the Core/λ-cluster restatement of
`lambda_tau1_apply_eq_of_not_mem_H_sat`, issue 9094 案 A): `(μ_j − λ)^{τ₁} = Ind_S^G(μ_j − λ)`
vanishes off `(H^#)^G` — both are induced from linear characters of `H = PC` with `P ⊄ Ker`
(the Core `mu_col` witness and the λ-cluster witness thread the *guarded*
`tau1S_apply_induce_sub`), so the difference is `H^#`-supported — whence
`λ^{τ₁}(x) = δ ∑_i η_{i1}(x)` there by the (13.3.c) column formula. -/
theorem _root_.solution [Finite G]
    [Invertible (Nat.card G : ℂ)]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) {x : G}
    (hx : x ∉ OddOrder.GroupTheory.conjClassSet (sharpSubgroup hyp.H)) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
      core.tau1S lam.lambda x
        = (δ : ℂ) * ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ x := by
  classical
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨j, δ, θμ, -, hδ, hθμirr, hθμ1, hθμP, hμInd, hμτ⟩ := core.mu_col_tau1_eta_col_one
  obtain ⟨θl, hθlirr, hθl1, hlamEq, x₀, hx₀P, hx₀ker⟩ := lam.lambda_induced_from_PC_linear
  have hθlP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θl) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  have hKnorm : (hyp.H.subgroupOf hyp.S).Normal := H_sharp_subgroupOf_normal hyp
  have hdiff : core.tau1S (∑ i : Fin hyp.q, hyp.mu i j) - core.tau1S lam.lambda
      = ClassFunction.induce hyp.S
          (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
            - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) := by
    rw [← map_sub, hμInd, hlamEq]
    have h := core.tau1S_apply_induce_sub θμ θl hθμirr hθlirr hθμP hθlP
    exact h.trans (by congr!)
  have hsupp : ∀ w : ↥hyp.S, (w : G) ∉ sharpSubgroup hyp.H →
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) w = 0 := by
    intro w hw
    rw [ClassFunction.sub_apply]
    by_cases hwH : (w : G) ∈ hyp.H
    · have hw1 : (w : G) = 1 := by
        by_contra hne
        exact hw ⟨hwH, fun h1 => hne (Set.mem_singleton_iff.mp h1)⟩
      have hw1' : w = 1 := Subtype.ext hw1
      subst hw1'
      rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one,
        OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθμ1, hθl1, sub_self]
    · rw [OddOrder.RepresentationTheory.ClassFunction.induce_eq_zero_of_not_mem_normal _
          (fun h => hwH (Subgroup.mem_subgroupOf.mp h)),
        OddOrder.RepresentationTheory.ClassFunction.induce_eq_zero_of_not_mem_normal _
          (fun h => hwH (Subgroup.mem_subgroupOf.mp h)), sub_self]
  have hvan : ClassFunction.induce hyp.S
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θμ
        - ClassFunction.induce (hyp.H.subgroupOf hyp.S) θl) x = 0 :=
    OddOrder.GroupTheory.IsTISubset.induce_apply_of_not_mem_conjClassSet _ hsupp hx
  refine ⟨δ, hδ, ?_⟩
  have hdv := congrArg (fun f : ClassFunction G ℂ => f x) hdiff
  simp only [ClassFunction.sub_apply] at hdv
  rw [hvan] at hdv
  have hμv := congrArg (fun f : ClassFunction G ℂ => f x) hμτ
  simp only [ClassFunction.smul_apply,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply] at hμv
  have hlamv : core.tau1S lam.lambda x = core.tau1S (∑ i : Fin hyp.q, hyp.mu i j) x :=
    (sub_eq_zero.mp hdv).symm
  exact hlamv.trans hμv

end OddOrder.Peterfalvi.S15
