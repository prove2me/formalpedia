-- Prove2me | solution 1 for PositivityTheory.CW.GradedNormalNilpotent.L_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:22:35.292028+00:00
-- url     : https://prove2.me/submissions/b309ccf8-e8cb-4006-b81b-0650a6580cf8

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CommutatorAdjointHolds
import Theorems.Thm_PositivityTheory_CW_GradedNormalNilpotent_coe_L
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.CW.GradedNormalNilpotent.coe_L

set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS Polynomial
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.GradedNormalNilpotent
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
variable {ε E}
variable (h : Hyp ε E)
namespace PositivityTheory.CW.GradedNormalNilpotent
theorem _root_.solution (j : ℕ) (x y : Module.End ℂ V) (hx : x ∈ U E j) (hy : y ∈ U E j) :
    L h j x hx - L h j y hy = L h j (x - y) (sub_mem hx hy) := by
  apply Subtype.ext; simp [sub_mul]
end PositivityTheory.CW.GradedNormalNilpotent
