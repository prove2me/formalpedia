-- Prove2me | solution 1 for ReciprocityTheory.PGsh.mono_mem_monoSpanF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:55.698678+00:00
-- url     : https://prove2.me/submissions/90397282-d688-4f8e-886d-6b488c7fd39e

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
theorem _root_.solution {w a : ℕ} (h : a ∈ monoIdx w) : (⇑(monoW w a) : ℍ → ℂ) ∈ monoSpanF w :=
  Submodule.subset_span ⟨⟨a, h⟩, rfl⟩
end ReciprocityTheory.PGsh
