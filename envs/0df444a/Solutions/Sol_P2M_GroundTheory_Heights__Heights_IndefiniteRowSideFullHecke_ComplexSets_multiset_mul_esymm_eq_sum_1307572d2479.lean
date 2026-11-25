-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_multiset_mul_esymm_eq_sum_1307572d2479
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:10.687239+00:00
-- url     : https://prove2.me/submissions/e56348a4-2e20-4899-9c93-a2be535b13fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPowerSumsEsymmAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPowerSumsEsymmAnalytic

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
open Finset
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map fun x => x ^ a.2).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun x : s => (x : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum s ℂ k)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe, MvPolynomial.psum,
    MvPolynomial.aeval_X] at h
  convert h using 4 with a _
  rw [Finset.sum_eq_multiset_sum]
  conv_lhs => rw [← Multiset.map_univ_coe s]
  rw [Multiset.map_map]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
