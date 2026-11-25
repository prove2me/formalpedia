-- Prove2me | solution 1 for PI.LocDualGen.EpS.mem_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:42.162527+00:00
-- url     : https://prove2.me/submissions/93d3d0a6-e569-4647-ba0d-c3628806c964

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Module
open PI PI.LocDualGen PI.LocDualGen.EpS
variable {K : Type} [Field K] {L : Type} [CommRing L] [Algebra K L]
variable [ValuativeRel K]
namespace PI.LocDualGen.EpS
theorem _root_.solution {c : K} (h : IsIntegral 𝒪[K] c) : c ∈ 𝒪[K] := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝒪[K]) (K := K)).mp h
  rw [← hy]; exact y.2
end PI.LocDualGen.EpS
