-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.eta_eq_of_norm_one_regular_value_eq
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:16:36.790907+00:00
-- url     : https://prove2.me/submissions/3176804b-75a1-487a-bca3-163cac7ebfcb

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapGridAlignment.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapGridAlignment

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapGridAlignment.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.9)(a)** (Coq `eq_in_cycTIiso`): a norm-one virtual character
agreeing with an eta-grid entry on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` equals
that entry globally.  The difference `ψ = η_A − φ` vanishes on the conjugacy
saturation of `Ŵ`, so its coefficient grid satisfies the (3.7) relation; each
of `η_A` and `φ` is norm-one, so `ψ` has at most two nonzero grid coefficients,
and the (3.8) small-support case forces them all to vanish.  In particular
`⟨φ, η_A⟩ = 1`, and the norm computation gives `ψ = 0`.

This is the rigidity behind Coq's `cycTIisoC`/`cycTIiso_irrel`: it upgrades the
regular-value agreement of two independently constructed sigma isometries to a
global equality of their grid entries, without any uniqueness assumption on
the isometries themselves. -/
theorem _root_.solution [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {φ : ClassFunction G ℂ} (hφZ : φ ∈ ZIrr G)
    (hφ1 : ClassFunction.inner φ φ = 1)
    (A : Fin base.q × Fin base.p)
    (hvals : ∀ w : G, w ∈ (base.W : Set G) →
      w ∉ (base.W1 : Set G) ∪ (base.W2 : Set G) →
      φ w = base.eta A.1 A.2 w) :
    φ = base.eta A.1 A.2 := by
  classical
  set ψ : ClassFunction G ℂ := base.eta A.1 A.2 - φ with hψ
  have hvanish : ∀ x ∈ conjClassSet
      ((base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G))), ψ x = 0 := by
    intro x hx
    obtain ⟨w, hw, g, hg⟩ := hx
    have hconj : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
    rw [← ψ.of_isConj hconj, hψ, ClassFunction.sub_apply,
      hvals w hw.1 hw.2, sub_self]
  -- the orthonormal grid family, packaged for the norm-one support bound
  have hgridZ : ∀ pq : Fin base.q × Fin base.p,
      base.eta pq.1 pq.2 ∈ ZIrr G := fun pq => eta_mem_ZIrr base pq.1 pq.2
  have hgridDiag : ∀ a : Fin base.q × Fin base.p,
      ClassFunction.inner (base.eta a.1 a.2) (base.eta a.1 a.2) = 1 :=
    fun a => by simpa using eta_orthonormal base a.1 a.1 a.2 a.2
  have hgridOff : ∀ a b : Fin base.q × Fin base.p, a ≠ b →
      ClassFunction.inner (base.eta a.1 a.2) (base.eta b.1 b.2) = 0 :=
    fun a b hab => by
      rw [eta_orthonormal base a.1 b.1 a.2 b.2, if_neg]
      rintro ⟨h1, h2⟩
      exact hab (Prod.ext h1 h2)
  -- ψ has at most two nonzero grid coefficients
  have hηNC := OddOrder.Peterfalvi.S05.ncard_inner_grid_ne_zero_le_one
    (fun pq : Fin base.q × Fin base.p => base.eta pq.1 pq.2)
    hgridZ hgridDiag hgridOff (hgridZ A) (hgridDiag A)
  have hφNC := OddOrder.Peterfalvi.S05.ncard_inner_grid_ne_zero_le_one
    (fun pq : Fin base.q × Fin base.p => base.eta pq.1 pq.2)
    hgridZ hgridDiag hgridOff hφZ hφ1
  have hNCset : {x : Fin base.q × Fin base.p |
      ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0}.ncard ≤ 2 := by
    have hsub : {x : Fin base.q × Fin base.p |
        ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0} ⊆
        {x : Fin base.q × Fin base.p |
          ClassFunction.inner (base.eta A.1 A.2) (base.eta x.1 x.2) ≠ 0} ∪
        {x : Fin base.q × Fin base.p |
          ClassFunction.inner φ (base.eta x.1 x.2) ≠ 0} := by
      intro x hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
      apply hx
      rw [hψ, ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
    calc {x : Fin base.q × Fin base.p |
          ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0}.ncard
        ≤ ({x : Fin base.q × Fin base.p |
            ClassFunction.inner (base.eta A.1 A.2) (base.eta x.1 x.2) ≠ 0} ∪
          {x : Fin base.q × Fin base.p |
            ClassFunction.inner φ (base.eta x.1 x.2) ≠ 0}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ {x : Fin base.q × Fin base.p |
            ClassFunction.inner (base.eta A.1 A.2) (base.eta x.1 x.2) ≠ 0}.ncard +
          {x : Fin base.q × Fin base.p |
            ClassFunction.inner φ (base.eta x.1 x.2) ≠ 0}.ncard :=
          Set.ncard_union_le _ _
      _ ≤ 2 := by omega
  have hNC : (Finset.univ.filter fun x : Fin base.q × Fin base.p =>
      ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0).card ≤ 2 := by
    calc (Finset.univ.filter fun x : Fin base.q × Fin base.p =>
          ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0).card
        = {x : Fin base.q × Fin base.p |
            ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0}.toFinset.card := by
          rw [Set.toFinset_ofPred]
      _ = {x : Fin base.q × Fin base.p |
            ClassFunction.inner ψ (base.eta x.1 x.2) ≠ 0}.ncard :=
          (Set.ncard_eq_toFinset_card' _).symm
      _ ≤ 2 := hNCset
  -- (3.7) + (3.8) small support: every grid coefficient of ψ vanishes
  have hzero := grid_eq_zero_of_relation_of_card_le_two
    base.three_le_q base.three_le_p
    (a := fun i j => ClassFunction.inner ψ (base.eta i j))
    ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩
    (fun i j => inner_eta_grid_relation base hvanish i j) hNC
  -- in particular `⟨φ, η_A⟩ = 1`, and the norm computation kills ψ
  have hA : ClassFunction.inner φ (base.eta A.1 A.2) = 1 := by
    have h0 := hzero A.1 A.2
    rw [hψ, ClassFunction.inner_sub_left] at h0
    linear_combination hgridDiag A - h0
  have hAsymm : ClassFunction.inner (base.eta A.1 A.2) φ = 1 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hA]
    simp
  have hself : ClassFunction.inner ψ ψ = 0 := by
    rw [hψ]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right]
    rw [hφ1, hA, hAsymm, hgridDiag A]
    ring
  have hfin := eq_zero_of_inner_self_re_eq_zero (φ := ψ) (by rw [hself]; simp)
  rw [hψ, sub_eq_zero] at hfin
  exact hfin.symm

end OddOrder.Peterfalvi.S16
