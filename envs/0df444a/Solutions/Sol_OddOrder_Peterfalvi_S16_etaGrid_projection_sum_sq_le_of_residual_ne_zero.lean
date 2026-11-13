-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.etaGrid_projection_sum_sq_le_of_residual_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:47.123964+00:00
-- url     : https://prove2.me/submissions/046c17f4-7b1b-4336-8b9e-ac2ccf0ca84f

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjection.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply
import Theorems.Thm_OddOrder_Peterfalvi_S16_etaGrid_projection_pythagorean

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapProjection.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G]

/-- An integer linear combination of the `eta`-grid is a virtual character. -/
theorem etaGridProjection_mem_ZIrr [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin base.q → Fin base.p → ℤ) :
    etaGridProjection base m ∈ ZIrr G := by
  classical
  rw [etaGridProjection]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  rw [Int.cast_smul_eq_zsmul]
  exact (ZIrr G).smul_mem (m i j) (eta_mem_ZIrr base i j)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), strict residual sharpens the projection bound.**
If the perpendicular residual of a norm-`p+1` virtual character is nonzero, it is itself a
nonzero virtual character and therefore has integral squared norm at least `1`.  Pythagoras then
sharpens the eta-grid coefficient bound from `sum mᵢⱼ² ≤ p+1` to `sum mᵢⱼ² ≤ p`. -/
theorem _root_.solution [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    {b : ClassFunction G ℂ} (hbZ : b ∈ ZIrr G)
    (hbnorm : ClassFunction.inner b b = (((base.p : ℤ) + 1) : ℂ))
    (m : Fin base.q → Fin base.p → ℤ)
    (hcoeff : ∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ))
    (hresidual : b - etaGridProjection base m ≠ 0) :
    (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤ (base.p : ℤ) := by
  have hf : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hi : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  have hresZ : b - etaGridProjection base m ∈ ZIrr G :=
    (ZIrr G).sub_mem hbZ (etaGridProjection_mem_ZIrr base m)
  obtain ⟨c, hsupp, hrepr, hnorm⟩ := mem_ZIrr_inner_self_eq_sum_sq hresZ
  have hsupport : c.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hresidual
    rw [hrepr, h]
    simp
  obtain ⟨a, ha⟩ := hsupport
  have hca : c a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have hresNormLower : (1 : ℤ) ≤ ∑ x ∈ c.support, (c x) ^ 2 := by
    calc
      (1 : ℤ) ≤ (c a) ^ 2 := by
        nlinarith [Int.one_le_abs hca, sq_abs (c a)]
      _ ≤ ∑ x ∈ c.support, (c x) ^ 2 := by
        exact Finset.single_le_sum (fun x _ => sq_nonneg (c x)) ha
  have hnormCast :
      ClassFunction.inner (b - etaGridProjection base m)
          (b - etaGridProjection base m) =
        ((∑ x ∈ c.support, (c x) ^ 2 : ℤ) : ℂ) := by
    rw [hnorm]
    push_cast
    rfl
  have hpyth := etaGrid_projection_pythagorean base b m hcoeff
  rw [hbnorm, hnormCast] at hpyth
  have hpythZ : (base.p : ℤ) + 1 =
      (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) +
        ∑ x ∈ c.support, (c x) ^ 2 := by
    exact_mod_cast hpyth
  omega

end OddOrder.Peterfalvi.S16
