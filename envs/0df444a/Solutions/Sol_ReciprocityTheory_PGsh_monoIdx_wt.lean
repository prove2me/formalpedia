-- Prove2me | solution 1 for ReciprocityTheory.PGsh.monoIdx_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:14.142866+00:00
-- url     : https://prove2.me/submissions/65c758b4-d340-481a-bf5c-5bbe91580eab

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
theorem _root_.solution {w a : ℕ} (h : a ∈ monoIdx w) : 4 * a + 6 * monoB w a = w := by
  simp only [monoIdx, Finset.mem_filter, Finset.mem_range] at h
  obtain ⟨_, h1, h2⟩ := h
  unfold monoB
  omega
end ReciprocityTheory.PGsh
