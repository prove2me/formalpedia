-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTermSharp_proof_82d3178e95d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:29.729113+00:00
-- url     : https://prove2.me/submissions/b8cc5c37-eebc-4e32-be68-ac936ddef9ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestTop

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
namespace GroundTheory.Heights₂.Heights
namespace RestTermSharp
theorem _root_.solution (h₁ : RestCutCaseSharp.Statement)
    (h₂ : RestCutTransportLast.Statement) (h₃ : RestCutTransportFirst.Statement)
    (h₄ : RestCutLieLast.Statement) (h₅ : RestCutLieFirst.Statement) :
    RestTermSharp.Statement := by
  intro f j k hf hj hk I hI vol hvol P hP B₀ hB φ
  by_cases hkj : k ≤ j
  · obtain ⟨hF, hJ⟩ := h₂ f j k hkj
    exact h₁ f j k k j .last (restLastEquiv j k) hf hj hk hk hj (Nat.add_comm k j)
      (Nat.mul_comm k j) hF hJ (h₄ f j k hkj) I hI vol hvol P hP B₀ hB φ
  · have hjk : j < k := by omega
    obtain ⟨hF, hJ⟩ := h₃ f j k hjk
    exact h₁ f j k j k .first (restFirstEquiv j k) hf hj hk hj hk rfl rfl hF hJ (h₅ f j k hjk)
      I hI vol hvol P hP B₀ hB φ
end RestTermSharp
end GroundTheory.Heights₂.Heights
