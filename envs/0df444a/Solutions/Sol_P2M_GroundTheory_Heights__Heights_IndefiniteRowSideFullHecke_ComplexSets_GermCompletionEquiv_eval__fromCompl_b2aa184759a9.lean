-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_eval__fromCompl_b2aa184759a9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:27.98705+00:00
-- url     : https://prove2.me/submissions/fe24cac2-1e53-429b-9807-76431045bef4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCompletionEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermPointIdealSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCompletionEquiv

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermCompletionEquiv
variable {σ : Type} [Fintype σ] (w : σ → ℂ)
variable (I : Ideal (MvPolynomial σ ℂ))
variable (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermCompletionEquiv
theorem _root_.solution (k : ℕ) (x : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :
    AdicCompletion.evalₐ (polyPointIdeal I w) k (fromCompl w I hH hP x) =
      (psiEquiv w I hH hP k).symm (AdicCompletion.evalₐ (germQuotPointIdeal I w) k x) := by
  rw [fromCompl, AdicCompletion.evalₐ_liftRingHom _ _
    (fun h => RingHom.ext fun x => fromCompl_compat w I hH hP h x)]
  try rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermCompletionEquiv
