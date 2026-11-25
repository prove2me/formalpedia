-- Prove2me | solution 1 for ReciprocityTheory.PGsh.monoIdx_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:39:30.485808+00:00
-- url     : https://prove2.me/submissions/a102f985-74e9-440a-ba12-c9ac4f8ba905

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries
namespace ReciprocityTheory.PGsh
theorem _root_.solution {w : ℕ} (he : Even w) (h2 : w ≠ 2) : ∃ a, a ∈ monoIdx w := by
  obtain ⟨m, rfl⟩ := he
  simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
  by_cases h : m % 2 = 0
  · exact ⟨(m + m) / 4, by omega, by omega, ⟨0, by omega⟩⟩
  · exact ⟨(m + m - 6) / 4, by omega, by omega, ⟨1, by omega⟩⟩
end ReciprocityTheory.PGsh
