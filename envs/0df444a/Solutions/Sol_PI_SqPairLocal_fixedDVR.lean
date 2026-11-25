-- Prove2me | solution 1 for PI.SqPairLocal.fixedDVR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:12.659307+00:00
-- url     : https://prove2.me/submissions/34f37bcd-47bf-4a68-a5d1-3c130da470bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub
import Theorems.Thm_PI_SqPairLocal_FixD_irr_sub
import Theorems.Thm_PI_SqPairLocal_FixD_dvr_sub
import Theorems.Thm_PI_SqPairLocal_FixD_hens_sub
import Theorems.Thm_PI_SqPairLocal_FixD_finite_sub
import Theorems.Thm_PI_SqPairLocal_mem_fixSub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open PI.SqPairLocal
open FixD
namespace PI.SqPairLocal
theorem _root_.solution : FixedDVR := by
  intro R _ _ _ _ _ σ hσ ϖ hϖ hσϖ
  have h : ϖ ∈ fixSub σ := (mem_fixSub σ ϖ).2 hσϖ
  haveI hd := dvr_sub σ hϖ h
  exact ⟨hd, hens_sub σ, finite_sub σ, fun h' => irr_sub σ hϖ h'⟩
end PI.SqPairLocal
