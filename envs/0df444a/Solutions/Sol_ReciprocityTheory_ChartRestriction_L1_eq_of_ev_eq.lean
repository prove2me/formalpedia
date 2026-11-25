-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.eq_of_ev_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:19.739572+00:00
-- url     : https://prove2.me/submissions/d952b4da-c3ad-4911-ae96-ff16e9d58ba8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eq_zero_of_ev_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_sub


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
theorem _root_.solution {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g)
    (h : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = ev g x) : f = g := by
  have h0 := eq_zero_of_ev_eq_zero (hf.sub hg) fun x hx0 hx1 => by
    rw [ev_sub hf hg hx1, h x hx0 hx1, sub_self]
  exact sub_eq_zero.mp h0
end ReciprocityTheory.ChartRestriction.L1
