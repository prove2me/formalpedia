-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntegralIndep_proof_4b5bf5e5d261
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:41.145423+00:00
-- url     : https://prove2.me/submissions/46149454-6848-4059-8ad2-8fd61d483be4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_chartInt_eq_posParts_786379f5608c

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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace IntegralIndep
theorem _root_.solution (h : PosPartIndep.Statement) : IntegralIndep.Statement := by
  intro n d J A A' f φ hP hd hA hA' hf hφ hi
  have e0 := h n d J A A' f φ hP hd hA hA' hf hφ
  have e1 := h n d J A A' (-f) φ hP hd hA hA' hf.neg hφ
  obtain ⟨iA, cA⟩ := IntegralIndep.chartInt_eq_posParts hA hf φ
  obtain ⟨iA', cA'⟩ := IntegralIndep.chartInt_eq_posParts hA' hf φ
  have hi' : Integrable (chartAbsDens J A' f φ) := iA'.2 (by rw [← e0, ← e1]; exact iA.1 hi)
  exact ⟨hi', by rw [cA hi, cA' hi', e0, e1]⟩
end IntegralIndep
end GroundTheory.Heights₂.Heights
