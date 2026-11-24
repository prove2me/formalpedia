-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.mem_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:59:07.864587+00:00
-- url     : https://prove2.me/submissions/4ccbf8a7-7df2-436f-ac4f-2cab3fffdfd8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h2 : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2
end ReciprocityTheory.ChartRestriction.L1
