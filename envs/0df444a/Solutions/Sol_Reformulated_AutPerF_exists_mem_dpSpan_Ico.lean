-- Prove2me | solution 1 for Reformulated.AutPerF.exists_mem_dpSpan_Ico
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:50:47.229479+00:00
-- url     : https://prove2.me/submissions/b6af6cd7-aa90-43e9-a944-3f3def35c440

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
import Theorems.Thm_Reformulated_AutPerF_dpSpan_mono
import Theorems.Thm_Reformulated_AutPerF_dp_mem_dpSpan
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {B : Type*} [CommRing B] [Algebra ℚ B]
variable {A : Type*} [CommRing A] [Algebra A B]
variable {ξ : A}
namespace Reformulated.AutPerF
theorem _root_.solution {x : B} (hx : x ∈ dpSpan B ξ Set.univ) :
    ∃ M, x ∈ dpSpan B ξ (Set.Ico 0 M) := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨m, -, rfl⟩ := hx; exact ⟨m + 1, dp_mem_dpSpan (by simp)⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨N, hN⟩ := hy
    exact ⟨max M N, add_mem (dpSpan_mono (Set.Ico_subset_Ico_right (le_max_left _ _)) hM)
      (dpSpan_mono (Set.Ico_subset_Ico_right (le_max_right _ _)) hN)⟩
  | smul a x _ hx => obtain ⟨M, hM⟩ := hx; exact ⟨M, Submodule.smul_mem _ a hM⟩
end Reformulated.AutPerF
