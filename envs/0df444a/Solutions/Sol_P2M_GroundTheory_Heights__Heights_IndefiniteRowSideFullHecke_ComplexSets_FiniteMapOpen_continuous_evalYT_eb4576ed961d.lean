-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_continuous_evalYT_eb4576ed961d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:51.059798+00:00
-- url     : https://prove2.me/submissions/4d3c994c-5ee8-41a5-bdaf-2e7b1ba50d9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
theorem _root_.solution {d : ℕ} (F : Polynomial (MvPolynomial (Fin d) ℂ)) (t : ℂ) :
    Continuous fun y => evalYT F y t := by
  have : (fun y => evalYT F y t) =
      fun y => ∑ k ∈ Finset.range (F.natDegree + 1), MvPolynomial.eval y (F.coeff k) * t ^ k := by
    funext y
    rw [evalYT, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  rw [this]
  exact continuous_finsetSum _ fun k _ => (MvPolynomial.continuous_eval _).mul continuous_const
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
