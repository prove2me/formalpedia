-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.ED.eq_of_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:59:53.773134+00:00
-- url     : https://prove2.me/submissions/6811af58-91db-4fa1-9d17-4640da63e65c

import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.ED
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.ED
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {w w' : ι → R}
    (h : ∀ x, w ⬝ᵥ x = w' ⬝ᵥ x) : w = w' := by
  funext i
  simpa using h (Pi.single i 1)
end ReciprocityTheory.PGsh.Up.ED
