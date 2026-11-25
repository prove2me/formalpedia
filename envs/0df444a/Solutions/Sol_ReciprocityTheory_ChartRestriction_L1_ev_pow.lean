-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.ev_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:05.267861+00:00
-- url     : https://prove2.me/submissions/7623ba99-6204-4448-bb54-a9b7af800182

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_pow


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
theorem _root_.solution {f : PowerSeries ℂ} (hf : Conv f) (n : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    ev (f ^ n) x = ev f x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ev_one]
  | succ n ih => rw [pow_succ, pow_succ, ev_mul (hf.pow n) hf hx, ih]
end ReciprocityTheory.ChartRestriction.L1
