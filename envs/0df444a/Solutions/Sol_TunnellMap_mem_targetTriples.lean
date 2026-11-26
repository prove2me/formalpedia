-- Prove2me | solution 1 for TunnellMap.mem_targetTriples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:41:46.28263+00:00
-- url     : https://prove2.me/submissions/babb184b-f9c7-4537-8314-639f437f638b

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
import Theorems.Thm_TunnellMap_mem_wCandidates
import Theorems.Thm_TunnellMap_mem_intRangeSym


set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} {w : Triple} (h : aForm w = n) :
    w ∈ targetTriples n := by
  have hform : 2 * w.x ^ 2 + w.y ^ 2 + 32 * w.z ^ 2 = n := h
  have hn : 0 ≤ n := by nlinarith [sq_nonneg w.x, sq_nonneg w.y, sq_nonneg w.z]
  have hxsq : w.x ^ 2 ≤ n := by nlinarith [sq_nonneg w.y, sq_nonneg w.z]
  have hysq : w.y ^ 2 ≤ n := by nlinarith [sq_nonneg w.x, sq_nonneg w.z]
  obtain ⟨hx₁, hx₂⟩ := coordinate_bounds_of_sq_le hn hxsq
  obtain ⟨hy₁, hy₂⟩ := coordinate_bounds_of_sq_le hn hysq
  refine List.mem_flatMap.mpr ⟨w.x, mem_intRangeSym hx₁ hx₂, ?_⟩
  refine List.mem_flatMap.mpr ⟨w.y, mem_intRangeSym hy₁ hy₂, ?_⟩
  refine List.mem_map.mpr ⟨w.z, ?_, rfl⟩
  refine mem_wCandidates ?_
  nlinarith [hform]
end TunnellMap
