-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_nonempty_heightOneSpectrum_8a32eca7b64e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:50.684847+00:00
-- url     : https://prove2.me/submissions/52a3c5d8-dbfe-49bd-9e8f-d88976bb3c0f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  refine ⟨⟨m, hm.isPrime, fun h ↦ NumberField.RingOfIntegers.not_isField K ?_⟩⟩
  exact Ring.isField_iff_maximal_bot.mpr (h ▸ hm)
end GroundTheory.Heights₂.Heights
