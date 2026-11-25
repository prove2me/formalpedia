-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.ev_xp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:55:26.793513+00:00
-- url     : https://prove2.me/submissions/a9691f78-f319-4638-89a3-25caeb4a4aea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_xp_term
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_xp_support
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
theorem _root_.solution (f : PowerSeries ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) : ev (xp k f) x = ev f (x ^ k) := by
  have hsupp : Function.support (fun n => PowerSeries.coeff n (xp k f) * x ^ n) ⊆
      Set.range (fun m : ℕ => k * m) := by
    intro n hn
    by_contra h
    exact hn (xp_support f k x n h)
  unfold ev
  rw [← (natMul_injective hk).tsum_eq hsupp]
  exact tsum_congr fun m => xp_term f hk x m
end ReciprocityTheory.ChartRestriction.L1
