-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_natCast_Cl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:53.378698+00:00
-- url     : https://prove2.me/submissions/dddb57a5-bad8-4790-b8b5-38fce570c47f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  rw [← PadicComplex.norm_extends' l (n : ℚ_[l])]
  congr 1
  simp
end ReciprocityTheory.ChartRestriction.L1
