-- Prove2me | solution 1 for OddOrder.GroupTheory.IsTISubset.induce_apply_of_mem_conj
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:54.082641+00:00
-- url     : https://prove2.me/submissions/3de1a6ae-ec0d-426a-b4d7-27bbec4b1b07

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/TISubset.lean
--   OddOrder/GroupTheory/TISubsetCounting.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

-- ===== OddOrder/GroupTheory/TISubset.lean =====
namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

namespace IsTISubset

variable {A : Set G} {L : Subgroup G}

/-- **TI overlap ⇒ conjugator ratio in `L`**: if two `G`-conjugates `g·A·g⁻¹` and `h·A·h⁻¹` of a
TI-subset `A` overlap (share a common element `g·a·g⁻¹ = h·b·h⁻¹` with `a, b ∈ A`), then the
conjugators differ by an element of the normalizer-bound: `h⁻¹·g ∈ L`.  This is the orbit-stabilizer
heart of the conjugate-union counting `|A^G| = [G : L]·|A|` (Peterfalvi (13.10.3) disjoint-union
counting `G = {1} ⊔ G₀ ⊔ (H^#)^G ⊔ (Q^#)^G`): distinct cosets `gL` give *disjoint* conjugates.
Proof: `(h⁻¹g)·a·(h⁻¹g)⁻¹ = h⁻¹·(g·a·g⁻¹)·h = h⁻¹·(h·b·h⁻¹)·h = b ∈ A`, so the TI condition
places `h⁻¹g ∈ L`. -/
theorem mem_of_conj_mem_conj (hA : IsTISubset A L) {g h a b : G}
    (ha : a ∈ A) (hb : b ∈ A) (hab : g * a * g⁻¹ = h * b * h⁻¹) : h⁻¹ * g ∈ L := by
  refine hA (h⁻¹ * g) ⟨a, ha, ?_⟩
  have key : (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = b := by
    have e : (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * a * g⁻¹) * h := by group
    rw [e, hab]; group
  rw [key]; exact hb

end IsTISubset

end OddOrder.GroupTheory

-- ===== OddOrder/GroupTheory/TISubsetCounting.lean =====
namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

namespace IsTISubset

open scoped Pointwise

/-- **Induced value on the TI-saturation** (Peterfalvi (7.2)/(13.2.e), value half): for a
TI-subset `A ⊆ L` with `L`-stable `A` and an `A`-supported class function `α` of `L`,
the induced class function `Ind_L^G α` takes the value `α(a)` at every conjugate
`g = y·a·y⁻¹` of every `a ∈ A`.  The nonvanishing induction summands are indexed by
exactly the coset `yL` (membership ⟸ `L`-stability, ⟹ the TI condition), each
contributing the class value `α(a)`; the normalization `⅟|L|` collapses the count.
This is what identifies the TI Dade isometry with `Ind_L^G` (Peterfalvi (2.5)+(7.2)). -/
theorem _root_.solution {k : Type*} [Field k] [Fintype G]
    {A : Set G} {L : Subgroup G} [Invertible (Nat.card ↥L : k)]
    (hTI : IsTISubset A L) (hAL : A ⊆ (L : Set G))
    (hstab : ∀ l ∈ L, MulAut.conj l • A = A)
    (α : OddOrder.RepresentationTheory.ClassFunction ↥L k)
    (hsupp : ∀ w : ↥L, (w : G) ∉ A → α w = 0)
    {a g y : G} (ha : a ∈ A) (hg : g = y * a * y⁻¹) :
    OddOrder.RepresentationTheory.ClassFunction.induce L α g = α ⟨a, hAL ha⟩ := by
  classical
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply]
  -- each summand is `α(a)` on the coset `yL` and `0` elsewhere
  have hterm : ∀ x : G, OddOrder.RepresentationTheory.ClassFunction.induceTerm L α x g
      = if y⁻¹ * x ∈ L then α ⟨a, hAL ha⟩ else 0 := by
    intro x
    by_cases hx : y⁻¹ * x ∈ L
    · rw [if_pos hx]
      -- `x⁻¹ g x = (y⁻¹x)⁻¹ a (y⁻¹x) ∈ A` by `L`-stability
      have hxa : x⁻¹ * g * x = (y⁻¹ * x)⁻¹ * a * (y⁻¹ * x) := by
        rw [hg]; group
      have hmemA : x⁻¹ * g * x ∈ A := by
        rw [hxa]
        have h1 := hstab _ (inv_mem hx)
        rw [← h1]
        refine Set.mem_smul_set.mpr ⟨a, ha, ?_⟩
        rw [MulAut.smul_def, MulAut.conj_apply]
        group
      have hmemL : x⁻¹ * g * x ∈ L := hAL hmemA
      rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_mem α hmemL]
      -- class value: `x⁻¹gx = (y⁻¹x)⁻¹ a (y⁻¹x)` is `L`-conjugate to `a`
      refine OddOrder.RepresentationTheory.ClassFunction.of_isConj α
        (isConj_iff.mpr ⟨⟨y⁻¹ * x, hx⟩, ?_⟩)
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hxa]
      group
    · rw [if_neg hx]
      by_cases hmemL : x⁻¹ * g * x ∈ L
      · rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_mem α hmemL]
        -- the value vanishes: `x⁻¹gx ∉ A`, else the TI condition forces `y⁻¹x ∈ L`
        refine hsupp _ (fun hmemA => hx ?_)
        have hconj : (x⁻¹ * y) * a * (x⁻¹ * y)⁻¹ = x⁻¹ * g * x := by
          rw [hg]; group
        have h1 : (1 : G)⁻¹ * (x⁻¹ * y) ∈ L :=
          hTI.mem_of_conj_mem_conj ha hmemA (by rw [hconj]; group)
        rw [inv_one, one_mul] at h1
        have := inv_mem h1
        rwa [mul_inv_rev, inv_inv] at this
      · rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_not_mem α hmemL]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero]
  -- the nonvanishing coset has exactly `|L|` elements
  have hcount : (Finset.univ.filter (fun x : G => y⁻¹ * x ∈ L)).card
      = Nat.card ↥L := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    refine Finset.card_bij
      (fun (x : G) (hx : x ∈ Finset.univ.filter (fun x : G => y⁻¹ * x ∈ L)) =>
        (⟨y⁻¹ * x, (Finset.mem_filter.mp hx).2⟩ : ↥L)) (fun _ _ => Finset.mem_univ _)
      ?_ ?_
    · intro x hx x' hx' hxx'
      have := congrArg Subtype.val hxx'
      simpa using this
    · intro l _
      refine ⟨y * (l : G), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [← mul_assoc, inv_mul_cancel, one_mul]; exact l.2⟩, ?_⟩
      apply Subtype.ext
      simp [← mul_assoc]
  rw [hcount, nsmul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]

end IsTISubset

end OddOrder.GroupTheory
