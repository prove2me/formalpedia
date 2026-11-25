-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_pullback_eq_33c6b9794aef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:00.142814+00:00
-- url     : https://prove2.me/submissions/5a06f695-f5b2-496e-9f27-34da1e9f53f6

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
theorem _root_.solution {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℂ) (P : MvPolynomial (Fin k) ℂ)
    (z : Fin n → ℂ) : eval z (GroundTheory.Heights₂.Heights.ComplexSets.pullback A P) = eval (A *ᵥ z) P := by
  unfold GroundTheory.Heights₂.Heights.ComplexSets.pullback
  change (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (aeval (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A) P) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hlin : (fun i => (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i))
      = A *ᵥ z := by
    funext i
    simp [GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]
  rw [hlin]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
