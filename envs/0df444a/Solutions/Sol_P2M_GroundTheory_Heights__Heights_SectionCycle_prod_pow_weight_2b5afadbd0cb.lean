-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_prod_pow_weight_2b5afadbd0cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:16:11.478018+00:00
-- url     : https://prove2.me/submissions/de4e755b-1dbb-40e0-9b8c-5c684feea7e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl

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
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution {M : Type*} [CommMonoid M] (t : ι → M) (s : Coord n →₀ ℕ) :
    ∏ k, t k ^ (Finsupp.weight (coordDeg n) s k) = s.prod fun v e ↦ t v.1 ^ e := by
  classical
  rw [Finsupp.weight_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, coordDeg, smul_eq_mul, Finsupp.prod]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [Finset.prod_eq_single v.1 (fun k _ hk ↦ by simp [hk]) (by simp)]
  simp
end GroundTheory.Heights₂.Heights.SectionCycle
