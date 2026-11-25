-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_exists_eval_line_ne_zero_0db500c9f83d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:31:37.607025+00:00
-- url     : https://prove2.me/submissions/a2b25344-a697-409d-989f-dc85a6cd5fc9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PolynomialFrame
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_pow_mul_prod_b08bb5bd44ba

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame
theorem _root_.solution {k : ℕ} (P : MvPolynomial (Fin k) ℂ) (v : Fin k → ℂ)
    (hv : eval v (homogeneousComponent P.totalDegree P) ≠ 0) (w : Fin k → ℂ) :
    ∃ t : ℂ, eval (w + t • v) P ≠ 0 := by
  by_contra! h
  set d := P.totalDegree with hd
  have hdeg : ∀ m ∈ P.support, m.degree ≤ d := fun m hm => le_totalDegree hm
  set H : ℂ → ℂ := fun s => ∑ m ∈ P.support,
    coeff m P * (s ^ (d - m.degree) * ∏ i ∈ m.support, (s * w i + v i) ^ m i) with hH
  have hHc : Continuous H := by
    simp only [hH]
    fun_prop
  have hzero : ∀ s : ℂ, s ≠ 0 → H s = 0 := by
    intro s hs
    have h1 := h s⁻¹
    rw [eval_eq] at h1
    have : H s = s ^ d * ∑ m ∈ P.support, coeff m P * ∏ i ∈ m.support, ((w + s⁻¹ • v) i) ^ m i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm (s ^ d), pow_mul_prod hs w v m (hdeg m hm)]
    rw [this, h1, mul_zero]
  have h0 : H 0 = 0 := by
    have h1 : Tendsto H (𝓝[≠] 0) (𝓝 (H 0)) := hHc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto H (𝓝[≠] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hzero s hs).symm)
    exact tendsto_nhds_unique h1 h2
  apply hv
  rw [homogeneousComponent_apply, map_sum, ← h0, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [eval_monomial, Finsupp.prod]
  split_ifs with hmd
  · rw [hmd, Nat.sub_self, pow_zero, one_mul]
    simp
  · have : d - m.degree ≠ 0 := by have := hdeg m hm; omega
    rw [zero_pow this, zero_mul, mul_zero]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame
