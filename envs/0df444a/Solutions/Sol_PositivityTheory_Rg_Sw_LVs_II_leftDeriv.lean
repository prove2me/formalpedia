-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.leftDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:48.160958+00:00
-- url     : https://prove2.me/submissions/f3dc44f9-c531-4750-808b-ddce8f94e384

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_core
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_reK_skew
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_imK_skew
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_reK_comm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_imK_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution : LeftDeriv := by
  intro n Kg _ _ _ _ _ _ μ _ ι hι hK F U hU hKU hF e he
  obtain ⟨i1, z1⟩ := core μ ι hι hK F U hU hKU hF (reK e) (reK_skew e) (reK_comm he)
  obtain ⟨i2, z2⟩ := core μ ι hι hK F U hU hKU hF (imK e) (imK_skew e) (imK_comm he)
  refine ⟨i1.add (i2.const_mul Complex.I), ?_⟩
  unfold dK
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, z1, z2]
  simp
end PositivityTheory.Rg.Sw.LVs.II
