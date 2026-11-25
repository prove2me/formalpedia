-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_ringKrullDim_of_mem_minimalPrimes_6ea4f2ae7cea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:29:36.614979+00:00
-- url     : https://prove2.me/submissions/b399b931-99c2-4a56-9f56-40196e26e2cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegreePositive
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_height_add_ringKrullDim_quotient
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_quotient_add_one_le
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive
variable {F : Type} [Field F] {ι₀ : Type} [Fintype ι₀]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive
theorem _root_.solution (q W : Ideal (MRing (fun _ : Unit => ι₀) F)) [q.IsPrime]
    (x : MRing (fun _ : Unit => ι₀) F) (hx : x ∉ q) (e : ℕ)
    (hdim : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hmin : W ∈ (q ⊔ Ideal.span {x}).minimalPrimes) :
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by
  have hWprime : W.IsPrime := hmin.1.1
  have hIW : q ≤ W := le_sup_left.trans hmin.1.2
  have hxW : x ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
  set B := MRing (fun _ : Unit => ι₀) F ⧸ q
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F q) (Ideal.Quotient.mkₐ_surjective F q)
  set W' : Ideal B := W.map (Ideal.Quotient.mk q)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk q x ∈ W' := Ideal.mem_map_of_mem _ hxW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = y := by
    cases h : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MRing (fun _ : Unit => ι₀) F ⧸ W)
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
end GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive
