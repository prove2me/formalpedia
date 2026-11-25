-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_eval_ne_zero_of_mem_nhds_2a51585cbfc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:04.037023+00:00
-- url     : https://prove2.me/submissions/5c44118a-c4d0-4b76-bf19-7c6e2ee5bb76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalOpenMapping

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
open MvPolynomial Topology Metric Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {k : ℕ} {P : MvPolynomial (Fin k) ℂ} (hP : P ≠ 0)
    {a : Fin k → ℂ} {N : Set (Fin k → ℂ)} (hN : N ∈ 𝓝 a) : ∃ y ∈ N, eval y P ≠ 0 := by
  by_contra! h
  apply hP
  have han : AnalyticOnNhd ℂ (fun y : Fin k → ℂ => eval y P) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial P
  have hz : (fun y : Fin k → ℂ => eval y P) =ᶠ[𝓝 a] 0 :=
    Filter.mem_of_superset hN (fun y hy => h y hy)
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) hz
  apply MvPolynomial.funext
  intro y
  simpa using h0 (Set.mem_univ y)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
