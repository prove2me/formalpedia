-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutCaseCompare_proof_4b6218470eeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:41.186868+00:00
-- url     : https://prove2.me/submissions/236296e4-8a0f-4207-bc45-4054cfc11e97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCaseCompare

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
namespace GroundTheory.Heights₂.Heights
namespace RestCutCaseCompare
theorem _root_.solution (h₁ : RestTerms.SameFactorBound.Statement)
    (h₂ : RestCutRestHom.Statement) (h₃ : RestCutStairNonzero.Statement)
    (h₄ : RestCutCompare.Statement) (h₅ : RestCutCompareReal.Statement) :
    RestCutCaseCompare.Statement := by
  intro f j k r a cs e hf hr ha hN hJ I hI
  have hD : flagDim f j k = RestTerms.topDegree f (r + a) := by
    simp only [flagDim, RestTerms.topDegree, hN]
  have hHh := (h₂ f r a cs).1
  have hJ0 : RestTerms.fibreDegree f r a cs ≠ 0 := (h₁ f r a cs hf hr ha).1
  have hst : RestTerms.flagIntegral f (r + a) (restStair f (r + a)) ≠ 0 := h₃ f (r + a) _ hHh hJ0
  refine ⟨restCompareConst f j k (r + a) e I, ?_, ?_⟩
  · exact h₅ f j k (r + a) e I _ (flagDim f j k) fun H' hH' => h₄ f j k (r + a) e I hI hst H' hH'
  · rw [← hJ]
    exact h₄ f j k (r + a) e I hI hst _ (hD ▸ hHh)
end RestCutCaseCompare
end GroundTheory.Heights₂.Heights
