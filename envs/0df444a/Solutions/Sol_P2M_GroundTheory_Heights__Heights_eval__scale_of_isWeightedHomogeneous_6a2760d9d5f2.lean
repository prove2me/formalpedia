-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval__scale_of_isWeightedHomogeneous_6a2760d9d5f2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:40.695193+00:00
-- url     : https://prove2.me/submissions/5583fb24-c077-438f-be22-eb909fca850e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {S : Type*} [CommRing S] [Fintype ι] (w : ι → S)
    (x : Coord n → S) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    eval₂ (Int.castRingHom S) (fun v ↦ w v.1 * x v) f =
      (∏ k, w k ^ δ k) * eval₂ (Int.castRingHom S) x f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [eval₂_sum, eval₂_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ ↦ ?_
  have hw : Finsupp.weight (coordDeg n) μ = δ := hf (mem_support_iff.mp hμ)
  have hδ : ∀ k, δ k = ∑ v ∈ μ.support with v.1 = k, μ v := by
    intro k
    rw [← hw, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    simp only [coordDeg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have hprod : (μ.prod fun v e ↦ w v.1 ^ e) = ∏ k, w k ^ δ k := by
    rw [Finsupp.prod]
    symm
    calc ∏ k, w k ^ δ k = ∏ k, ∏ v ∈ μ.support with v.1 = k, w v.1 ^ μ v := by
          refine Finset.prod_congr rfl fun k _ ↦ ?_
          rw [hδ k, ← Finset.prod_pow_eq_pow_sum]
          refine Finset.prod_congr rfl fun v hv ↦ ?_
          rw [(Finset.mem_filter.mp hv).2]
      _ = ∏ v ∈ μ.support, w v.1 ^ μ v := Finset.prod_fiberwise _ _ _
  rw [← hprod]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  ring
end GroundTheory.Heights₂.Heights
