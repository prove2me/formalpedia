-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.xp_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:00.180629+00:00
-- url     : https://prove2.me/submissions/ef2a1e7e-7f40-41e2-a0dd-f5dd40c97d04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (f : PowerSeries ℂ) (k : ℕ) (x : ℂ) :
    ∀ n ∉ Set.range (fun m : ℕ => k * m), PowerSeries.coeff n (xp k f) * x ^ n = 0 := by
  intro n hn
  have hkn : ¬ k ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
  rw [xp, PowerSeries.coeff_mk, if_neg hkn, zero_mul]
end ReciprocityTheory.ChartRestriction.L1
