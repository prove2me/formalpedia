-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_ker_aeval_chart_24e855cde06c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:50.755218+00:00
-- url     : https://prove2.me/submissions/af2a8d28-6bc6-4f1b-8c9c-49d71da01209

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_pow_mul_aeval_eq_0699d72cc976

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
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (hI : IsHomogIdeal I)
    (t : Fin n → F) (hτ : aeval (genPt I) (linForm t) ≠ 0) :
    RingHom.ker (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I)).toRingHom =
      I ⊔ Ideal.span {linForm t - 1} := by
  set ξ := genPt I
  set τ := aeval ξ (linForm t)
  have hξ : ∀ g, aeval ξ g = 0 ↔ g ∈ I := by
    intro g
    have : aeval ξ g = algebraMap (MvPolynomial (Fin n) F ⧸ I) (FractionRing (MvPolynomial (Fin n) F ⧸ I))
        (Ideal.Quotient.mk I g) := by
      have h : (aeval ξ : MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I)) =
          (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ I) (FractionRing (MvPolynomial (Fin n) F ⧸ I))).comp
            (Ideal.Quotient.mkₐ F I) := by
        ext j
        simp [ξ, genPt]
      rw [h]
      rfl
    rw [this, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  apply le_antisymm
  · intro g hg
    rw [RingHom.mem_ker] at hg
    change aeval (τ⁻¹ • ξ) g = 0 at hg
    have hG := pow_mul_aeval_eq t ξ hτ g
    rw [hg, mul_zero, eq_comm, hξ] at hG
    have hGg : (∑ d ∈ Finset.range (g.totalDegree + 1),
        linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) - g ∈ Ideal.span {linForm t - 1} := by
      rw [show (∑ d ∈ Finset.range (g.totalDegree + 1),
          linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) - g =
          ∑ d ∈ Finset.range (g.totalDegree + 1),
            (linForm t ^ (g.totalDegree - d) * homogeneousComponent d g - homogeneousComponent d g) by
        rw [Finset.sum_sub_distrib, sum_homogeneousComponent]]
      refine Ideal.sum_mem _ fun d _ => ?_
      rw [Ideal.mem_span_singleton, ← sub_one_mul]
      exact (sub_one_dvd_pow_sub_one _ _).mul_right _
    have : g = (∑ d ∈ Finset.range (g.totalDegree + 1),
        linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) -
        ((∑ d ∈ Finset.range (g.totalDegree + 1),
        linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) - g) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hG) (Ideal.mem_sup_right hGg)
  · refine sup_le ?_ ?_
    · intro g hg
      rw [RingHom.mem_ker]
      change aeval (τ⁻¹ • ξ) g = 0
      have hG := pow_mul_aeval_eq t ξ hτ g
      have hmem : (∑ d ∈ Finset.range (g.totalDegree + 1),
          linForm t ^ (g.totalDegree - d) * homogeneousComponent d g) ∈ I :=
        Ideal.sum_mem _ fun d _ => Ideal.mul_mem_left _ _ (hI g hg d)
      rw [← hξ] at hmem
      rw [hmem] at hG
      exact (mul_eq_zero.mp hG).resolve_left (pow_ne_zero _ hτ)
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      change aeval (τ⁻¹ • ξ) (linForm t - 1) = 0
      have : aeval (τ⁻¹ • ξ) (linForm t) = τ⁻¹ * τ := by
        simp [τ, linForm, Finset.mul_sum, mul_left_comm]
      rw [map_sub, this, inv_mul_cancel₀ hτ, map_one, sub_self]
end GroundTheory.Heights₂.Heights.ChartKernel
