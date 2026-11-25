-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeDimComponent_proof_closed_0c228e09f176
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:37.510189+00:00
-- url     : https://prove2.me/submissions/9a191e2f-cf77-448b-ab75-8b1a902cf17b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimComponent
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_height_add_ringKrullDim_quotient
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_quotient_add_one_le
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_iff_7a22acaba460
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_sup_span_linForm_b5797af1aa52


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights
namespace ConeDimComponent
theorem _root_.solution : ConeDimComponent.Statement := by
  intro F _ n e I W u hI hdim hu hW
  obtain ⟨hmin, hrel⟩ := hW
  have hWprime : W.IsPrime := hmin.1.1

  have hJ : IsHomogIdeal (I ⊔ Ideal.span {linForm u}) := isHomogIdeal_sup_span_linForm hI.isHomog u
  have hproj : IsProjPrime W := by
    classical
    have hJh := (isHomogIdeal_iff _).mp hJ
    refine ⟨hWprime, (isHomogIdeal_iff W).mpr ?_, hrel⟩
    set core := (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal
    have hcore_prime : core.IsPrime := hWprime.homogeneousCore
    have hJcore : I ⊔ Ideal.span {linForm u} ≤ core := by
      rw [← hJh.toIdeal_homogeneousCore_eq_self]
      exact Ideal.homogeneousCore_mono _ hmin.1.2
    have hle : core ≤ W := Ideal.toIdeal_homogeneousCore_le _ _
    have heq : core = W := le_antisymm hle (hmin.2 ⟨hcore_prime, hJcore⟩ hle)
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  refine ⟨hproj, ?_⟩

  have hIprime : I.IsPrime := hI.isPrime
  have hIW : I ≤ W := le_sup_left.trans hmin.1.2
  have huW : linForm u ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
  set B := MvPolynomial (Fin n) F ⧸ I
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I)
      (Ideal.Quotient.mkₐ_surjective F I)
  set W' : Ideal B := W.map (Ideal.Quotient.mk I)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hu
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk I (linForm u) ∈ W' := Ideal.mem_map_of_mem _ huW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = y := by
    cases h : ringKrullDim (MvPolynomial (Fin n) F ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) F ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ e := by
    have : y + 1 ≤ (e : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = y := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top
    (ENat.natCast_ne_top e) hyle)
  have h3 : ((e + 1 : ℕ) : ℕ∞) ≤ 1 + m := by rw [← h2]; gcongr
  have h4 : e + 1 ≤ 1 + m := by exact_mod_cast h3
  have h5 : m ≤ e := by exact_mod_cast hyle
  have : m = e := by omega
  subst this
  rfl
end ConeDimComponent
end GroundTheory.Heights₂.Heights
