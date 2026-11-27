-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_proof_c997225cfa1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:57:12.052714+00:00
-- url     : https://prove2.me/submissions/b858b559-b312-4d09-8247-475c6581e707

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCompletionEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermPointIdealSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCompletionEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_eval__fromCompl_b2aa184759a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_fromCompl_toCompl_e9d2f81547ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermCompletionEquiv_toCompl_fromCompl_24991331a9a6

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
open GermCompletionEquiv
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GermCompletionEquiv
theorem _root_.solution (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement) :
    GermCompletionEquiv.Statement := by
  intro σ _ I w
  refine ⟨RingEquiv.ofRingHom (fromCompl w I hH hP) (toCompl w I)
    (RingHom.ext fun x => fromCompl_toCompl w I hH hP x) (RingHom.ext fun x => toCompl_fromCompl w I hH hP x),
    fun q => ?_⟩
  change fromCompl w I hH hP _ = _
  refine AdicCompletion.ext_evalₐ fun k => ?_
  rw [evalₐ_fromCompl, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, RingEquiv.symm_apply_eq]
  exact (psi_mk w I k q).symm
end GermCompletionEquiv
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
