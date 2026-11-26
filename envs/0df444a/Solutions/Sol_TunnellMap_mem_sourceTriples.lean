-- Prove2me | solution 1 for TunnellMap.mem_sourceTriples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:31:18.268011+00:00
-- url     : https://prove2.me/submissions/99a7667f-6ae7-4035-8e36-dd479cec46af

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
import Theorems.Thm_TunnellMap_mem_intRangeSym
import Theorems.Thm_TunnellMap_mem_zCandidates

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} {w : Triple} (h : bForm w = n) :
    w ∈ sourceTriples n := by
  have hform : 2 * w.x ^ 2 + w.y ^ 2 + 8 * w.z ^ 2 = n := h
  have hn : 0 ≤ n := by nlinarith [sq_nonneg w.x, sq_nonneg w.y, sq_nonneg w.z]
  have hxsq : w.x ^ 2 ≤ n := by nlinarith [sq_nonneg w.y, sq_nonneg w.z]
  have hysq : w.y ^ 2 ≤ n := by nlinarith [sq_nonneg w.x, sq_nonneg w.z]
  obtain ⟨hx₁, hx₂⟩ := coordinate_bounds_of_sq_le hn hxsq
  obtain ⟨hy₁, hy₂⟩ := coordinate_bounds_of_sq_le hn hysq
  refine List.mem_flatMap.mpr ⟨w.x, mem_intRangeSym hx₁ hx₂, ?_⟩
  refine List.mem_flatMap.mpr ⟨w.y, mem_intRangeSym hy₁ hy₂, ?_⟩
  refine List.mem_map.mpr ⟨w.z, ?_, rfl⟩
  refine mem_zCandidates ?_
  nlinarith [hform]
end TunnellMap
