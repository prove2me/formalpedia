-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.etaGrid_projection_pythagorean
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:09:08.492929+00:00
-- url     : https://prove2.me/submissions/ee696e3b-adf8-4fbd-838a-6ca398af8fe7

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Pythagoras for the full `eta`-grid.**  If the integer coefficients `m_ij` are the
Fourier coefficients of `phi` on the orthonormal grid, then the squared norm of `phi` is the
sum of their squares plus the squared norm of the perpendicular residual. -/
theorem _root_.solution [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (phi : ClassFunction G ℂ) (m : Fin hyp.q → Fin hyp.p → ℤ)
    (hcoeff : ∀ i j, ClassFunction.inner phi (hyp.eta i j) = (m i j : ℂ)) :
    ClassFunction.inner phi phi =
      ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) +
        ClassFunction.inner (phi - etaGridProjection hyp m)
          (phi - etaGridProjection hyp m) := by
  classical
  set X : ClassFunction G ℂ := etaGridProjection hyp m with hX
  set Y : ClassFunction G ℂ := phi - X with hY
  have hXeta : ∀ (k : Fin hyp.q) (l : Fin hyp.p),
      ClassFunction.inner X (hyp.eta k l) = (m k l : ℂ) := by
    intro k l
    rw [hX, etaGridProjection, inner_sum_left]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun i _ hik => ?_)]
    · rw [inner_sum_left,
        Finset.sum_eq_single_of_mem l (Finset.mem_univ _) (fun j _ hjl => ?_)]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
          if_pos ⟨rfl, rfl⟩, mul_one]
      · rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
          if_neg (by rintro ⟨-, rfl⟩; exact hjl rfl), mul_zero]
    · rw [inner_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [ClassFunction.inner_smul_left, eta_orthonormal hyp,
        if_neg (by rintro ⟨rfl, -⟩; exact hik rfl), mul_zero]
  have hsum_sq : ∀ psi : ClassFunction G ℂ,
      (∀ (k : Fin hyp.q) (l : Fin hyp.p),
        ClassFunction.inner psi (hyp.eta k l) = (m k l : ℂ)) ->
      ClassFunction.inner psi X =
        ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) := by
    intro psi hpsi
    rw [hX, etaGridProjection, inner_sum_right]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_right, hpsi i j, star_intCast]
    ring
  have hXY : ClassFunction.inner X Y = 0 := by
    have hXX := hsum_sq X hXeta
    have hXphi : ClassFunction.inner X phi =
        ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hsum_sq phi hcoeff, star_intCast]
    rw [hY, ClassFunction.inner_sub_right, hXphi, hXX, sub_self]
  have hYX : ClassFunction.inner Y X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXY, star_zero]
  have hphiXY : phi = X + Y := by rw [hY]; abel
  have hsplit : ClassFunction.inner phi phi =
      ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) +
        ClassFunction.inner Y Y := by
    calc
      ClassFunction.inner phi phi = ClassFunction.inner (X + Y) (X + Y) := by rw [← hphiXY]
      _ = ClassFunction.inner X X + ClassFunction.inner X Y +
          (ClassFunction.inner Y X + ClassFunction.inner Y Y) := by
        rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
          ClassFunction.inner_add_right]
      _ = ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) +
          ClassFunction.inner Y Y := by rw [hXY, hYX, hsum_sq X hXeta]; ring
  simpa [hX, hY] using hsplit

end OddOrder.Peterfalvi.S16
