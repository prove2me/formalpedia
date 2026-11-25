-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sum_val_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:11:13.93192+00:00
-- url     : https://prove2.me/submissions/1a5ce8e0-9307-4fe8-a2f8-fb0f1b17b798

import Definitions.Def_ReciprocityTheory_DualLattices_MonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_SumValCoord
import Theorems.Thm_ReciprocityTheory_PGsh_Up_sum_val_zmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι) :
    ∑ α : ι → ZMod p, (α j).val = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2) := by
  have h := (Equiv.funSplitAt j (ZMod p)).sum_comp (fun q => q.1.val)
  simp only [Equiv.funSplitAt_apply] at h
  rw [h, Fintype.sum_prod_type]
  simp only [sum_const, card_univ, smul_eq_mul]
  rw [← Finset.mul_sum, sum_val_zmod]
  congr 1
  rw [Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
end ReciprocityTheory.PGsh.Up
