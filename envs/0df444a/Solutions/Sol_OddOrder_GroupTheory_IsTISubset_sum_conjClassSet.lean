-- Prove2me | solution 1 for OddOrder.GroupTheory.IsTISubset.sum_conjClassSet
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:08:35.84467+00:00
-- url     : https://prove2.me/submissions/83c48337-410f-4b26-ac82-266490665bcf

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

/-- **Conjugation-invariant sums over a TI-saturation** (issue 9011): for a TI-subset `A`
with normalizer-bound `L` that stabilizes it (`A^l = A` for `l ∈ L`), and a
conjugation-invariant `f`, the sum of `f` over the saturation `𝒞_G(A) = A^G` is `[G : L]`
times the sum over `A`.  The saturation is the disjoint union of the conjugates `g • A`
indexed by the cosets `gL` (disjointness = the TI condition via `mem_of_conj_mem_conj`),
and each conjugate contributes the same sum (conjugation-invariance of `f`).

Weighted refinement of `OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset`; the
Parseval-split engine of the Peterfalvi (13.10) norm estimates. -/
theorem _root_.solution [Finite G] {A : Set G} {L : Subgroup G}
    {M : Type*} [AddCommMonoid M] (f : G → M)
    (hTI : IsTISubset A L) (hstab : ∀ l ∈ L, MulAut.conj l • A = A)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x) :
    ∑ x ∈ (Set.toFinite (conjClassSet A)).toFinset, f x
      = L.index • ∑ a ∈ (Set.toFinite A).toFinset, f a := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (G ⧸ L) := Fintype.ofFinite _
  -- The coset-indexed conjugate family `B (gL) = g • A` (well-defined by `L`-stability).
  have hwd : ∀ g₁ g₂ : G, QuotientGroup.leftRel L g₁ g₂ →
      MulAut.conj g₁ • A = MulAut.conj g₂ • A := by
    intro g₁ g₂ hrel
    rw [QuotientGroup.leftRel_apply] at hrel
    calc MulAut.conj g₁ • A
        = MulAut.conj g₁ • (MulAut.conj (g₁⁻¹ * g₂) • A) := by rw [hstab _ hrel]
      _ = MulAut.conj g₂ • A := by rw [← mul_smul, ← map_mul, mul_inv_cancel_left]
  set B : G ⧸ L → Set G := Quotient.lift (fun g => MulAut.conj g • A) hwd with hBdef
  have hBval : ∀ g : G, B (QuotientGroup.mk g) = MulAut.conj g • A := fun g => rfl
  -- The saturation is the union of the conjugates.
  have hunion : conjClassSet A = ⋃ q : G ⧸ L, B q := by
    ext y
    rw [mem_conjClassSet, Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht, g, rfl⟩
      refine ⟨QuotientGroup.mk g, ?_⟩
      rw [hBval, Set.mem_smul_set]
      exact ⟨t, ht, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    · rintro ⟨q, hq⟩
      obtain ⟨g, rfl⟩ := Quotient.exists_rep q
      rw [hBval, Set.mem_smul_set] at hq
      obtain ⟨a, ha, rfl⟩ := hq
      exact ⟨a, ha, g, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  -- Distinct cosets give disjoint conjugates (the TI condition).
  have hdisj : ∀ q q' : G ⧸ L, q ≠ q' → Disjoint (B q) (B q') := by
    intro q q' hqq'
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨g', rfl⟩ := Quotient.exists_rep q'
    rw [hBval, hBval, Set.disjoint_left]
    rintro y hy hy'
    rw [Set.mem_smul_set] at hy hy'
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨a', ha', heq⟩ := hy'
    have he : g * a * g⁻¹ = g' * a' * g'⁻¹ := by
      rw [MulAut.smul_def, MulAut.smul_def, MulAut.conj_apply, MulAut.conj_apply] at heq
      exact heq.symm
    refine hqq' (Quotient.sound ?_)
    change (QuotientGroup.leftRel L) g g'
    rw [QuotientGroup.leftRel_apply,
      show g⁻¹ * g' = (g'⁻¹ * g)⁻¹ from by group]
    exact L.inv_mem (hTI.mem_of_conj_mem_conj ha ha' he)
  -- Each conjugate sums to the `A`-sum (conjugation-invariance).
  have hBsum : ∀ q : G ⧸ L,
      ∑ x ∈ (Set.toFinite (B q)).toFinset, f x = ∑ a ∈ (Set.toFinite A).toFinset, f a := by
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    have himg : (Set.toFinite (B (QuotientGroup.mk g))).toFinset
        = Finset.image (fun a => g * a * g⁻¹) (Set.toFinite A).toFinset := by
      ext x
      rw [Set.Finite.mem_toFinset, hBval, Set.mem_smul_set, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, (Set.toFinite A).mem_toFinset.mpr ha,
          by rw [MulAut.smul_def, MulAut.conj_apply]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, (Set.toFinite A).mem_toFinset.mp ha,
          by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    have hinj : ∀ a ∈ (Set.toFinite A).toFinset, ∀ b ∈ (Set.toFinite A).toFinset,
        g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a _ b _ hab => by
      have := congrArg (fun x => g⁻¹ * x * g) hab
      simpa [mul_assoc] using this
    rw [himg, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun a _ => hf g a
  -- Assemble: sum over the union = index • the `A`-sum.
  have hsplit : (Set.toFinite (conjClassSet A)).toFinset
      = Finset.univ.biUnion (fun q : G ⧸ L => (Set.toFinite (B q)).toFinset) := by
    ext x
    rw [Set.Finite.mem_toFinset, hunion, Set.mem_iUnion, Finset.mem_biUnion]
    exact ⟨fun ⟨q, hq⟩ => ⟨q, Finset.mem_univ q, (Set.toFinite _).mem_toFinset.mpr hq⟩,
      fun ⟨q, _, hq⟩ => ⟨q, (Set.toFinite _).mem_toFinset.mp hq⟩⟩
  rw [hsplit, Finset.sum_biUnion (fun q _ q' _ hqq' =>
    Finset.disjoint_left.mpr (fun _ hx hx' =>
      Set.disjoint_left.mp (hdisj q q' hqq') ((Set.toFinite _).mem_toFinset.mp hx)
        ((Set.toFinite _).mem_toFinset.mp hx')))]
  rw [Finset.sum_congr rfl (fun q _ => hBsum q), Finset.sum_const, Finset.card_univ,
    Subgroup.index, Nat.card_eq_fintype_card]

end IsTISubset

end OddOrder.GroupTheory
