-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.etaGrid_zeroColumn_projection_of_coefficients_eq_column
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:20.96265+00:00
-- url     : https://prove2.me/submissions/dc012cb2-d7f6-4bc1-9c30-2820952e326a

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjectionRigidity.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjectionRigidity.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), the zero-column coefficient shape is the
zero-column eta projection.**  This is the instance-stable linear-algebra
bridge from the surviving coefficient alternative to `eq_proj_eta`. -/
theorem _root_.solution [Finite G]
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (b : ClassFunction G ℂ) (m : Fin base.q → Fin base.p → ℤ)
    (hm : ∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ))
    (hcolumn : ∀ i j,
      m i j = if j = ⟨0, base.p_prime.pos⟩ then 1 else 0) :
    ∀ j : Fin base.p,
      ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b =
        ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j)
          (∑ i : Fin base.q, base.eta i ⟨0, base.p_prime.pos⟩) := by
  have hfintype : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  intro j
  have hleft : ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b =
      if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by
    calc
      ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j) b =
          star (ClassFunction.inner b (base.eta ⟨0, base.q_prime.pos⟩ j)) :=
        OddOrder.RepresentationTheory.inner_conj_symm _ _
      _ = star (m ⟨0, base.q_prime.pos⟩ j : ℂ) := by rw [hm]
      _ = if j = ⟨0, base.p_prime.pos⟩ then 1 else 0 := by
        rw [hcolumn]
        split <;> simp
  have hright : ClassFunction.inner (base.eta ⟨0, base.q_prime.pos⟩ j)
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
  exact hleft.trans hright.symm

end OddOrder.Peterfalvi.S16
