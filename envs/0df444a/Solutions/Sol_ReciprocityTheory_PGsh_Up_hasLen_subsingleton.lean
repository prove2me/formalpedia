-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.hasLen_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:36:44.233871+00:00
-- url     : https://prove2.me/submissions/f876bd7c-6523-482e-9f74-048495a1bb7f

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonOf
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm
import Definitions.Def_ReciprocityTheory_DualLattices_InvolutionPermApplyZero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (M : Type) [AddCommGroup M] [Module R M] [Subsingleton M] : HasLen v R M 1 := by
  unfold HasLen
  refine ⟨0, fun i => i.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, ?_⟩
  simp
end ReciprocityTheory.PGsh.Up
