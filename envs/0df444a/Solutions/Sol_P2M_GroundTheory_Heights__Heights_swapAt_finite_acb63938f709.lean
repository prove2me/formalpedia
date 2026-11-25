-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_swapAt_finite_acb63938f709
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:55.481798+00:00
-- url     : https://prove2.me/submissions/58350ef6-c55a-42b6-80c7-c6a24eee1f33

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
theorem _root_.solution (v₀ : HeightOneSpectrum (𝓞 K)) : {v | swapAt v₀ v ≠ 1}.Finite := by
  refine (Set.finite_singleton v₀).subset fun v hv ↦ ?_
  by_contra h
  rw [Set.mem_singleton_iff] at h
  exact hv (by simp only [swapAt, if_neg h])
end GroundTheory.Heights₂.Heights
