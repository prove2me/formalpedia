-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_natCast_Cl_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:29:56.889069+00:00
-- url     : https://prove2.me/submissions/19f062f3-6638-49a4-b896-6c31a493e96d

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
theorem _root_.solution {n : ℕ} (hn : ¬ l ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by
  rw [norm_natCast_Cl, Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hn
end ReciprocityTheory.ChartRestriction.L1
