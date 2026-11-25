-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:42:52.080475+00:00
-- url     : https://prove2.me/submissions/ddd4796c-5fa3-405d-9873-d69814a987d0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviChain
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_wd_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviV_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_contDiffAt_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_wd_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_leviV_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ComplexConjugate Filter Topology Matrix
namespace ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
private theorem ofReal_sqNorm_projPerp_mulVec {p : ℕ} (G w : Fin p → ℂ) (hG : G ≠ 0) :
    ((sqNorm (projPerp G *ᵥ w) : ℝ) : ℂ) = ((sqNorm w : ℝ) : ℂ) -
      ((Complex.normSq (∑ i, conj (G i) * w i) : ℝ) : ℂ) / ((sqNorm G : ℝ) : ℂ) := by
  have hc : ∀ v : Fin p → ℂ, ((sqNorm v : ℝ) : ℂ) = ∑ i, v i * conj (v i) := by
    intro v
    unfold sqNorm
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => (Complex.mul_conj _).symm
  have hpos : 0 < sqNorm G := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hG
    unfold sqNorm
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  have hS0 : ((sqNorm G : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hP : ∀ i, (projPerp G *ᵥ w) i =
      w i - ((sqNorm G : ℝ) : ℂ)⁻¹ * (G i * ∑ j, conj (G j) * w j) := by
    intro i
    simp only [projPerp, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hst : star (G j) = conj (G j) := rfl
    rw [hst]
    ring
  have key : ∀ i, (projPerp G *ᵥ w) i * conj ((projPerp G *ᵥ w) i) =
      w i * conj (w i)
        - ((sqNorm G : ℝ) : ℂ)⁻¹ * conj (∑ j, conj (G j) * w j) * (conj (G i) * w i)
        - ((sqNorm G : ℝ) : ℂ)⁻¹ * (∑ j, conj (G j) * w j) * (G i * conj (w i))
        + ((sqNorm G : ℝ) : ℂ)⁻¹ * ((sqNorm G : ℝ) : ℂ)⁻¹ * (∑ j, conj (G j) * w j) *
            conj (∑ j, conj (G j) * w j) * (G i * conj (G i)) := by
    intro i
    rw [hP i, map_sub, map_mul, map_mul, map_inv₀, Complex.conj_ofReal]
    ring
  have h2 : ∑ i, G i * conj (w i) = conj (∑ j, conj (G j) * w j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Complex.conj_conj]
  rw [hc (projPerp G *ᵥ w), hc w, ← Complex.mul_conj]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h2, ← hc G]
  field_simp
  ring
end ReciprocityTheory.L2DbarEstimates.H
end

set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution : LeviLogNormSqStatement := by
  intro n p g x ξ hg hne
  have hSi : ∀ i, ContDiffAt ℝ 2 (fun y => Complex.normSq (g i y)) x :=
    fun i => contDiffAt_normSq_comp (hg i)
  have hS : ContDiffAt ℝ 2 (fun y => sqNorm (fun i => g i y)) x := by
    unfold sqNorm
    exact ContDiffAt.sum fun i _ => hSi i
  have hSx : 0 < sqNorm (fun i => g i x) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    unfold sqNorm
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  have hS0 : ((sqNorm (fun i => g i x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hSx.ne'
  have hlog : ContDiffAt ℝ 2 Real.log (sqNorm (fun i => g i x)) :=
    Real.contDiffAt_log.mpr hSx.ne'
  have chain : leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((deriv Real.log (sqNorm (fun i => g i x)) : ℝ) : ℂ) *
          leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ +
        ((deriv (deriv Real.log) (sqNorm (fun i => g i x)) : ℝ) : ℂ) *
          ((Complex.normSq (∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j) :
            ℝ) : ℂ) :=
    leviChain n Real.log (fun y => sqNorm (fun i => g i y)) x ξ hS hlog
  have d1 : deriv Real.log (sqNorm fun i => g i x) = (sqNorm fun i => g i x)⁻¹ :=
    Real.deriv_log _
  have d2 : deriv (deriv Real.log) (sqNorm fun i => g i x) = -((sqNorm fun i => g i x) ^ 2)⁻¹ := by
    rw [Real.deriv_log']
    exact deriv_inv
  have hwd : ∀ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
      ∑ i, wd n j (g i) x * conj (g i x) := by
    intro j
    unfold sqNorm
    rw [wd_ofReal_sum fun i => (hSi i).differentiableAt (by first | norm_num | simp)]
    exact Finset.sum_congr rfl fun i _ => wd_normSq_comp (hg i)
  have hlv : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
      ∑ i, ((Complex.normSq ((wJac n p g x *ᵥ ξ) i) : ℝ) : ℂ) := by
    unfold sqNorm
    rw [leviV_ofReal_sum hSi ξ]
    exact Finset.sum_congr rfl fun i _ => leviV_normSq_comp (hg i) ξ
  have hs : ∑ j, (∑ i, wd n j (g i) x * conj (g i x)) * ξ j =
      ∑ i, conj (g i x) * (wJac n p g x *ᵥ ξ) i := by
    simp only [Matrix.mulVec, dotProduct, wJac, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hW : ((sqNorm (wJac n p g x *ᵥ ξ) : ℝ) : ℂ) =
      ∑ i, ((Complex.normSq ((wJac n p g x *ᵥ ξ) i) : ℝ) : ℂ) := by
    unfold sqNorm
    rw [Complex.ofReal_sum]
  rw [chain, d1, d2, hlv]
  simp only [hwd]
  rw [hs, Complex.ofReal_div, ofReal_sqNorm_projPerp_mulVec _ _ hne, hW]
  push_cast
  field_simp
  ring
end ReciprocityTheory.L2DbarEstimates.H
