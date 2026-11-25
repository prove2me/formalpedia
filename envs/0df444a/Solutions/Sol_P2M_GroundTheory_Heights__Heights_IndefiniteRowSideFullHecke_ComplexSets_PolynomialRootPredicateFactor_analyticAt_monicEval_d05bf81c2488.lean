-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_analyticAt_monicEval_d05bf81c2488
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:32:00.31869+00:00
-- url     : https://prove2.me/submissions/65acc058-9ee9-4853-8b05-e16119ea6ed2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor

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
open Polynomial Filter Topology Classical
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
theorem _root_.solution {d m : ℕ} (F : ℕ → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (T : ℂ)
    (hF : ∀ k, AnalyticAt ℂ (F k) t) :
    AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => u.2 ^ m + ∑ k ∈ Finset.range m, F k u.1 * u.2 ^ k) (t, T) := by
  have h1 : ∀ k, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => F k u.1 * u.2 ^ k) (t, T) := fun k =>
    ((hF k).comp_of_eq analyticAt_fst rfl).fun_mul (analyticAt_snd.fun_pow k)
  exact (analyticAt_snd.fun_pow m).fun_add (Finset.analyticAt_fun_sum _ fun k _ => h1 k)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor
