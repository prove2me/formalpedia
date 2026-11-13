-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.exists_etaGrid_intProjection_of_inner_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:08:12.132874+00:00
-- url     : https://prove2.me/submissions/ef83c3c8-f1c9-48c0-86e3-a2e5f5cfbabe

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

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9)(a), integral eta-grid projection with norm bound.**
A virtual character `b` of norm `p+1` has integer Fourier coefficients `mᵢⱼ`
against the orthonormal eta-grid. Pythagoras writes its norm as the sum of
coefficient squares plus the perpendicular residual norm, hence
`sum mᵢⱼ² ≤ p+1`.

For the T-side bridge, `b = τ_T(ν₀-ζ)` and the norm premise is supplied by
`exists_typeIII_induced_primeTIDifference_with_norm`. -/
theorem _root_.solution [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    [fintypeG : Fintype G]
    [invertibleG : Invertible (Nat.card G : ℂ)]
    {b : ClassFunction G ℂ} (hbZ : b ∈ ZIrr G)
    (hbnorm : ClassFunction.inner b b = (((base.p : ℤ) + 1) : ℂ)) :
    ∃ m : Fin base.q → Fin base.p → ℤ,
      (∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ)) ∧
      ClassFunction.inner b b =
        ((∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) : ℂ) +
          ClassFunction.inner (b - etaGridProjection base m)
            (b - etaGridProjection base m) ∧
      (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤
        (base.p : ℤ) + 1 := by
  have hf : fintypeG =
      OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype := Subsingleton.elim _ _
  subst fintypeG
  have hi : invertibleG =
      OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG := Subsingleton.elim _ _
  subst invertibleG
  let witness : ∀ i : Fin base.q, ∀ j : Fin base.p,
      ∃ z : ℤ, ClassFunction.inner b (base.eta i j) = (z : ℂ) :=
    fun i j => ClassFunction.inner_mem_ZIrr_int hbZ (eta_mem_ZIrr base i j)
  let m : Fin base.q → Fin base.p → ℤ := fun i j => (witness i j).choose
  have hcoeff : ∀ i j, ClassFunction.inner b (base.eta i j) = (m i j : ℂ) :=
    fun i j => (witness i j).choose_spec
  have hpyth := etaGrid_projection_pythagorean base b m hcoeff
  have hbound : (∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) ≤
      (base.p : ℤ) + 1 := by
    have hnn : (0 : ℝ) ≤
        (ClassFunction.inner (b - etaGridProjection base m)
          (b - etaGridProjection base m)).re :=
      inner_self_re_nonneg _
    have hre := congrArg Complex.re hpyth
    rw [Complex.add_re, Complex.intCast_re] at hre
    have hbRe : (ClassFunction.inner b b).re = (base.p : ℝ) + 1 := by
      rw [hbnorm]
      norm_num
    rw [hbRe] at hre
    have hle :
        ((∑ i : Fin base.q, ∑ j : Fin base.p, (m i j) ^ 2 : ℤ) : ℝ) ≤
          (base.p : ℝ) + 1 := by linarith
    exact_mod_cast hle
  exact ⟨m, hcoeff, hpyth, hbound⟩

end OddOrder.Peterfalvi.S16
