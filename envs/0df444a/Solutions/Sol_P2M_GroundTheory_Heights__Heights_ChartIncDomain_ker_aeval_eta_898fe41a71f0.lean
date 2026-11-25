-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIncDomain_ker_aeval_eta_898fe41a71f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:48:13.283642+00:00
-- url     : https://prove2.me/submissions/3ce18540-f243-44b1-94d8-d843b9f021d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_smul_of_isHomogeneous_7eddd2d173b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncDomain_isHomogeneous_linForm_5e6e05fede50
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_genPt_93dec95d46e3

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
open GroundTheory.Heights₂.Heights.ChartIncDomain
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIncDomain
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (hI : IsProjPrime I)
    (ht : linForm t ∉ I) :
    have := hI.isPrime
    RingHom.ker (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I) :
        MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I)) =
      I ⊔ Ideal.span {linForm t - 1} := by
  have := hI.isPrime
  set ξ := genPt I
  set τ := aeval ξ (linForm t)
  have hτ : τ ≠ 0 := by
    rw [show τ = _ from aeval_genPt I (linForm t), Ne, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact ht
  have hhom : ∀ (p : MvPolynomial (Fin n) F) (d : ℕ), p.IsHomogeneous d →
      aeval (τ⁻¹ • ξ) p = τ⁻¹ ^ d * aeval ξ p := fun p d hp => aeval_smul_of_isHomogeneous hp _ _
  have hcomp : ∀ (g : MvPolynomial (Fin n) F), aeval (τ⁻¹ • ξ) g =
      ∑ d ∈ Finset.range (g.totalDegree + 1), τ⁻¹ ^ d * aeval ξ (homogeneousComponent d g) := by
    intro g
    conv_lhs => rw [← sum_homogeneousComponent g]
    rw [map_sum]
    exact Finset.sum_congr rfl fun d _ => hhom _ _ (homogeneousComponent_isHomogeneous d g)
  apply le_antisymm
  · intro g hg
    rw [RingHom.mem_ker] at hg
    set D := g.totalDegree
    set G := ∑ d ∈ Finset.range (D + 1), homogeneousComponent d g * linForm t ^ (D - d)
    have hGξ : aeval ξ G = τ ^ D * aeval (τ⁻¹ • ξ) g := by
      rw [hcomp, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdD : d ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
      rw [map_mul, map_pow, ← mul_assoc, mul_comm (aeval ξ _)]
      congr 1
      rw [← Nat.sub_add_cancel hdD, pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hτ, one_pow,
        mul_one, Nat.sub_add_cancel hdD]
    have hGI : G ∈ I := by
      have h0 : aeval ξ G = 0 := by
        rw [hGξ]
        have : (aeval (τ⁻¹ • ξ) : MvPolynomial (Fin n) F →ₐ[F] _) g = 0 := hg
        rw [this, mul_zero]
      rw [aeval_genPt, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
      exact h0
    set J := I ⊔ Ideal.span {linForm t - 1}
    have h1 : Ideal.Quotient.mk J (linForm t) = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    have hG : Ideal.Quotient.mk J G = Ideal.Quotient.mk J g := by
      simp only [G, map_sum, map_mul, map_pow, h1, one_pow, mul_one]
      rw [← map_sum, sum_homogeneousComponent]
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hG, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left hGI
  · refine sup_le ?_ ?_
    · intro g hg
      rw [RingHom.mem_ker]
      change aeval (τ⁻¹ • ξ) g = 0
      rw [hcomp]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [aeval_genPt, (Ideal.Quotient.eq_zero_iff_mem).mpr (hI.isHomog g hg d), map_zero, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      change aeval (τ⁻¹ • ξ) (linForm t - 1) = 0
      rw [map_sub, map_one, hhom _ 1 (isHomogeneous_linForm t), pow_one, inv_mul_cancel₀ hτ, sub_self]
end GroundTheory.Heights₂.Heights.ChartIncDomain
