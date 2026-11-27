-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthCutGlobal_proof_647ed36447f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:03:01.730603+00:00
-- url     : https://prove2.me/submissions/bcc6d48e-7d8e-43cd-80c3-47164eca4406

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_eq_c804c0ba1527

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
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
namespace GroundTheory.Heights₂.Heights.LengthCutGlobal
theorem _root_.solution : LengthCutGlobal.Statement.{u, v} := by
  intro C _ _ P _ y M _ _ _ hnil hPID hy hmax hinj
  obtain ⟨k, hk⟩ := hnil
  rw [Submodule.ideal_span_singleton_smul]
  refine lengths_eq P y hPID hy hmax k M (fun p hp m => ?_) hinj
  rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
  rw [hp, zero_smul]
end GroundTheory.Heights₂.Heights.LengthCutGlobal
