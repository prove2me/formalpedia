-- Prove2me | solution 1 for OddOrder.Isaacs.Ch06.IsFrobeniusGroup.conjComplement
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:14.588423+00:00
-- url     : https://prove2.me/submissions/42ce4357-b73c-4aac-8283-7f16a1aee04d

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
import Mathlib.GroupTheory.SpecificGroups.ZGroup

-- ===== OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean =====
namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

open scoped commutatorElement

open OddOrder.Isaacs.Ch04

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

/-- A conjugate `A^g` of the complement of a Frobenius group `G = N ⋊ A` is again a Frobenius
complement (the normal kernel `N` is fixed by conjugation).  Used to choose a complement
containing a prescribed kernel-disjoint subgroup. -/
theorem _root_.solution {G : Type*} [Group G] [Finite G] {N A : Subgroup G}
    (h : IsFrobeniusGroup G N A) (g : G) :
    IsFrobeniusGroup G N (A.map (MulAut.conj g).toMonoidHom) := by
  have := h.isNormal
  have hAg_card : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv.symm
  -- `x ∈ A^g ↔ g⁻¹ x g ∈ A`.
  have hmem : ∀ x : G, x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have : g⁻¹ * (MulAut.conj g).toMonoidHom b * g = b := by simp [MulAut.conj_apply]; group
      rwa [this]
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply]; group⟩
  have hNdisj : N ⊓ A = ⊥ := disjoint_iff.mp h.isComplement.disjoint
  refine ⟨h.isNormal, ?_, h.ne_bot_kernel, ?_, ?_⟩
  · -- `IsComplement' N A^g` via card and disjointness.
    rw [Subgroup.isComplement'_iff_card_mul_and_disjoint]
    refine ⟨by rw [hAg_card]; exact h.isComplement.card_mul_card, ?_⟩
    rw [Subgroup.disjoint_def]
    intro x hxN hxAg
    rw [hmem] at hxAg
    have hgxg : g⁻¹ * x * g ∈ N ⊓ A :=
      ⟨by simpa using h.isNormal.conj_mem x hxN g⁻¹, hxAg⟩
    rw [hNdisj, Subgroup.mem_bot] at hgxg
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, hgxg]; group
  · -- `A^g ≠ ⊥`.
    intro hbot
    exact h.ne_bot_complement (Subgroup.card_eq_one.mp (by rw [← hAg_card, hbot,
        Subgroup.card_bot]))
  · -- conjugation Frobenius for `A^g`, transferred along `g`.
    intro a haAg ha1 n hnN hn1 hfix
    rw [hmem] at haAg
    have hmN : g⁻¹ * n * g ∈ N := by simpa using h.isNormal.conj_mem n hnN g⁻¹
    have hb1 : g⁻¹ * a * g ≠ 1 := fun he => ha1 (by
      have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      rw [this, he]; group)
    have hm1 : g⁻¹ * n * g ≠ 1 := fun he => hn1 (by
      have : n = g * (g⁻¹ * n * g) * g⁻¹ := by group
      rw [this, he]; group)
    -- `a n a⁻¹ = n` transfers to `(g⁻¹ a g)(g⁻¹ n g)(g⁻¹ a g)⁻¹ = g⁻¹ n g`.
    have hbm : (g⁻¹ * a * g) * (g⁻¹ * n * g) * (g⁻¹ * a * g)⁻¹ = g⁻¹ * n * g := by
      have : (g⁻¹ * a * g) * (g⁻¹ * n * g) * (g⁻¹ * a * g)⁻¹ = g⁻¹ * (a * n * a⁻¹) * g := by group
      rw [this, hfix]
    exact h.conj_frobenius _ haAg hb1 _ hmN hm1 hbm

end OddOrder.Isaacs.Ch06
