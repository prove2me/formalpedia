-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.qExp_AA_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:39:04.638627+00:00
-- url     : https://prove2.me/submissions/b3b4c568-abdd-4271-835d-d2f836077230

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_analytic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_aC_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isMF_AA


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
theorem _root_.solution (n : ℕ) : qExpansion 1 (fun τ => AA τ ^ n) = aC ^ n := by
  induction n with
  | zero =>
    have : (fun τ => AA τ ^ 0) = (1 : ℍ → ℂ) := by funext τ; simp
    rw [this, qExpansion_one, pow_zero]
  | succ n ih =>
    have : (fun τ => AA τ ^ (n + 1)) = (fun τ => AA τ ^ n) * AA := by funext τ; simp [pow_succ]
    rw [this, qExpansion_mul (isMF_AA.pow n).analytic isMF_AA.analytic, ih, pow_succ, aC_eq]
end ReciprocityTheory.ChartRestriction.L1
