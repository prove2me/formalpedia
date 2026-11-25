-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_eval_eq_pow_add_sum_6a2fccd0c6eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:29.391226+00:00
-- url     : https://prove2.me/submissions/3ea0e840-6e23-4695-869a-b84bf68bddf5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral

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
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {p : Polynomial ℂ} {m : ℕ} (hp : p.Monic) (hd : p.natDegree = m) (t : ℂ) :
    p.eval t = t ^ m + ∑ j : Fin m, p.coeff j * t ^ (j : ℕ) := by
  rw [Polynomial.eval_eq_sum_range, hd, Finset.sum_range_succ, ← hd, Polynomial.coeff_natDegree,
    hp.leadingCoeff, hd, one_mul, add_comm,
    Fin.sum_univ_eq_sum_range (fun j => p.coeff j * t ^ j) m]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
