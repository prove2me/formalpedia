-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerm_proof_1a24724251bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:38.309683+00:00
-- url     : https://prove2.me/submissions/d737643f-8ab4-40ef-81b5-1821335c7564

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
namespace RestTerm
theorem _root_.solution (h : RestTermSharp.Statement) : RestTerm.Statement := by
  refine ⟨1.6, by norm_num, ?_⟩
  intro f j k hf hj hk I hI vol hvol P hP B₀ hB φ
  obtain ⟨hex, hall⟩ := h f j k hf hj hk I hI vol hvol P hP B₀ hB φ
  refine ⟨hex, fun Q hQ => ?_⟩
  obtain ⟨hs, hb⟩ := hall Q hQ
  refine ⟨hs, hb.trans ?_⟩
  have hmin : (1 : ℝ) ≤ ((min j k : ℕ) : ℝ) := by exact_mod_cast le_min hj hk
  have hnn : 0 ≤ (((f * j * k : ℕ) : ℝ) + 1) * vol * |I (degreeInput f j k)| := by positivity
  have := mul_nonneg (sub_nonneg.2 hmin) hnn
  nlinarith
end RestTerm
end GroundTheory.Heights₂.Heights
