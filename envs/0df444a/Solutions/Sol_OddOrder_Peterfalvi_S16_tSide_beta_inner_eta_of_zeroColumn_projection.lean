-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.tSide_beta_inner_eta_of_zeroColumn_projection
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:06:32.659834+00:00
-- url     : https://prove2.me/submissions/5751d6e7-e829-48d3-b1f2-ee226be7e0d1

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapCross.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapCross.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped BigOperators

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)/(14.9), projection-to-row reduction.**

Let `b` be the T-side Dade image of `β_{T,0}`.  The output of the
`FTtype34_structure` projection calculation is that every `η_{0j}`
has the same inner product with `b` as with the zero-column sum
`∑ᵢ η_{i0}`.  Orthonormality of the η-grid then gives
`⟨b,η_{0j}⟩ = [j=0]`.

This theorem is the fully formal linear-algebraic passage from the deep
(11.9) projection statement to Coq's `o_eta0_betaT0`; the remaining
character-theoretic input is now exactly `hproj`. -/
theorem _root_.solution [Finite G]
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (b : ClassFunction G ℂ)
    (hproj : ∀ j : Fin base.p,
      ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b =
        ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j)
          (∑ i : Fin base.q,
            base.eta i ⟨0, base.p_prime.pos⟩))
    (j : Fin base.p) :
    ClassFunction.inner b (base.eta ⟨0, base.q_prime.pos⟩ j) =
      if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by
  have hfintype : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have hsum : ClassFunction.inner
      (base.eta ⟨0, base.q_prime.pos⟩ j)
      (∑ i : Fin base.q, base.eta i ⟨0, base.p_prime.pos⟩) =
        if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    by_cases hj : j = ⟨0, base.p_prime.pos⟩
    · subst j
      rw [Finset.sum_eq_single_of_mem (⟨0, base.q_prime.pos⟩ : Fin base.q)
        (Finset.mem_univ _) (fun i _ hi => by
          rw [eta_orthonormal, if_neg]
          rintro ⟨h, -⟩
          exact hi h.symm)]
      rw [eta_orthonormal, if_pos ⟨rfl, rfl⟩]
      simp
    · simp only [if_neg hj]
      apply Finset.sum_eq_zero
      intro i _
      rw [eta_orthonormal, if_neg]
      exact fun h => hj h.2
  calc
    ClassFunction.inner b (base.eta ⟨0, base.q_prime.pos⟩ j) =
        star (ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b) :=
      OddOrder.RepresentationTheory.inner_conj_symm _ _
    _ = star (if j = ⟨0, base.p_prime.pos⟩ then 1 else 0) := by rw [hproj j, hsum]
    _ = if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by split <;> simp

end OddOrder.Peterfalvi.S16
