-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.TypeICoherent78Data.etaGrid_projection_sub_beta_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:07:20.473968+00:00
-- url     : https://prove2.me/submissions/98f81282-06c1-4ccb-a08d-7107bdfafdad

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
--   OddOrder/Peterfalvi/S16_PairingBessel.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/QuadraticTerm.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_8

namespace Hypothesis78

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype L]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- Variant of `sourceDiffNormEvaluation_of_inner_values` using irreducibility of
the chosen `ζ` instead of a raw self-inner-product evaluation. -/
theorem sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
    (H78 : Hypothesis78 G A L)
    (hind_norm :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H) (H78.hyp76.zeta H78.ind1H) =
        (H78.complementIndex : ℂ))
    (hzeta_ind :
      ClassFunction.inner (H78.hyp76.zeta H78.zetaDistinct)
        (H78.hyp76.zeta H78.ind1H) = 0)
    (hind_zeta :
      ClassFunction.inner (H78.hyp76.zeta H78.ind1H)
        (H78.hyp76.zeta H78.zetaDistinct) = 0)
    (hzeta_irr : IsIrreducibleCharacter (H78.hyp76.zeta H78.zetaDistinct)) :
    H78.SourceDiffNormEvaluation :=
  H78.sourceDiffNormEvaluation_of_inner_values
    hind_norm hzeta_ind hind_zeta
    (H78.zetaDistinct_inner_self_eq_one_of_irreducible hzeta_irr)

end Hypothesis78

end Section_7_8

end OddOrder.Peterfalvi.S09

-- ===== OddOrder/Peterfalvi/S16_PairingCoherence.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- The zeta family of `h78` is the placed induced family (definitional). -/
theorem h78_zeta_eq (i : Fin (data.n + 1)) :
    (data.h78 hG).hyp76.zeta i = data.zeta i := rfl

/-- The distinguished index of `h78` is `0` (definitional). -/
theorem h78_zetaDistinct_eq : (data.h78 hG).zetaDistinct = 0 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The distinguished `ζ_0` is irreducible** (Frobenius kernel induction,
[Is] Thm 6.34). -/
theorem h78_zeta_irreducible :
    IsIrreducibleCharacter ((data.h78 hG).hyp76.zeta (data.h78 hG).zetaDistinct) := by
  have := data.kernelIn_normal
  rw [data.h78_zetaDistinct_eq, data.h78_zeta_eq]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_PairingBessel.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- `e = [L : H]` as the `subgroupOf` index (bundle form). -/
theorem complementIndex_eq :
    (data.h78 hG).complementIndex = (data.kernelIn).index :=
  complementIndex_eq_subgroupOf_index (data.h78 hG)

/-- **`‖ζ_{ind1H}‖² = e`** (the induced principal norm). -/
theorem zeta_ind1H_normSq :
    ClassFunction.inner ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H))
      ((data.h78 hG).hyp76.zeta ((data.h78 hG).ind1H))
      = ((data.h78 hG).complementIndex : ℂ) := by
  have := data.kernelIn_normal
  rw [data.complementIndex_eq hG]
  change ClassFunction.inner
      (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ))
      (ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ))
    = ((data.kernelIn).index : ℂ)
  rw [data.triv]
  exact induce_trivialChar_normSq_eq_index data.kernelIn

/-- **The (7.8) source-side norm evaluation** `‖Ind 1_H − ζ‖² = e + 1`. -/
theorem sourceDiffNormEvaluation :
    (data.h78 hG).SourceDiffNormEvaluation := by
  have := data.kernelIn_normal
  refine (data.h78 hG).sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
    (data.zeta_ind1H_normSq hG) ?_ ?_ (data.h78_zeta_irreducible hG)
  · exact induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj 0 data.ind1H
      (Ne.symm data.ind1H_ne_zero)
  · exact induce_family_orthogonal_of_injective data.kernelIn data.θ data.inj data.ind1H 0
      data.ind1H_ne_zero

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped BigOperators

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.11.2), unit norm of the removed character.**
Let `X = Σ m_ij eta_ij` be the rigid signed grid projection and
`chi = X - beta`.  If every `m_ij` is `+1` or `-1`, the complement index is
`p*q`, and `m_ij = ⟨beta, eta_ij⟩`, then orthonormality gives
`⟨X,X⟩ = ⟨beta,X⟩ = ⟨X,beta⟩ = p*q`.  The Dade source-norm
evaluation gives `⟨beta,beta⟩ = p*q + 1`, hence `⟨chi,chi⟩ = 1`.

This is the norm-one input used to classify `chi` as the coherent image of
the distinguished character or the negative image of its conjugate. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (data : TypeICoherent78Data L)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ)
    (hpm : ∀ i j, m i j = 1 ∨ m i j = -1)
    (heq : (data.h78 hG).complementIndex = hyp.p * hyp.q)
    (hcoeff : ∀ i j,
      ClassFunction.inner (data.h78 hG).beta (hyp.eta i j) = (m i j : ℂ)) :
    ClassFunction.inner
        (etaGridProjection hyp m - (data.h78 hG).beta)
        (etaGridProjection hyp m - (data.h78 hG).beta) = 1 := by
  classical
  have := data.kernelIn_normal
  set H78 := data.h78 hG with hH78
  set X : ClassFunction G ℂ := etaGridProjection hyp m with hX
  set S : ℤ := ∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 with hS
  have hsquare : ∀ i j, (m i j) ^ 2 = 1 := by
    intro i j
    rcases hpm i j with h | h <;> rw [h] <;> norm_num
  have hsum : S = (hyp.p * hyp.q : ℕ) := by
    rw [hS]
    simp_rw [hsquare]
    simp [Nat.mul_comm]
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
        ClassFunction.inner psi (hyp.eta k l) = (m k l : ℂ)) →
      ClassFunction.inner psi X = (S : ℂ) := by
    intro psi hpsi
    rw [hX, etaGridProjection, inner_sum_right, hS]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ClassFunction.inner_smul_right, hpsi i j, star_intCast]
    ring
  have hXX : ClassFunction.inner X X = (S : ℂ) := hsum_sq X hXeta
  have hbetaX : ClassFunction.inner H78.beta X = (S : ℂ) := by
    apply hsum_sq H78.beta
    simpa [hH78] using hcoeff
  have hXbeta : ClassFunction.inner X H78.beta = (S : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hbetaX, star_intCast]
  have hbetaRe := H78.betaNormSq_eq_complementIndex_add_one
    (data.sourceDiffNormEvaluation hG)
  change (ClassFunction.inner H78.beta H78.beta).re =
      (H78.complementIndex : ℝ) + 1 at hbetaRe
  have hbeta : ClassFunction.inner H78.beta H78.beta =
      (((H78.complementIndex : ℝ) + 1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa using hbetaRe
    · rw [OddOrder.RepresentationTheory.inner_self_eq_realCast]
      simp
  change ClassFunction.inner (X - H78.beta) (X - H78.beta) = 1
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hXX, hXbeta, hbetaX, hbeta]
  rw [hsum, heq]
  push_cast
  ring

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16
