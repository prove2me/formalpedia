-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_l_Cl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:13.662837+00:00
-- url     : https://prove2.me/submissions/eb653335-f564-426b-9ec4-832ff8a76343

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormNatCastClOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_natCast_Cl

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
theorem _root_.solution : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_Cl, Padic.norm_p]
end ReciprocityTheory.ChartRestriction.L1
