-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.discriminantColengthStatement_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:36:45.693213+00:00
-- url     : https://prove2.me/submissions/db358ef2-f65f-4837-9fdf-17884affd0cb

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLe
import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatementHolds
import Theorems.Thm_ReciprocityTheory_PGsh_Up_colength_sq_blockVandermonde
import Theorems.Thm_ReciprocityTheory_PGsh_Up_colength_sq_mul_le
import Theorems.Thm_ReciprocityTheory_PGsh_Up_valuation_pairwiseDifferenceProduct_pow_le_colength_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : DiscriminantColengthStatement := by
  intro C _ _ v R _ _ _ _ n a hinj ha
  exact ⟨fun s F S hF hS => colength_sq_blockVandermonde a s F S hF hS,
    fun s M S Mτ hM hτ hS => valuation_pairwiseDifferenceProduct_pow_le_colength_sq C v n a s M S Mτ hM hτ hS,
    fun s h A F M' S Mτ hF _ hM' hτ hS => colength_sq_mul_le a hinj ha s h A F M' S Mτ hF hM' hτ hS⟩
end ReciprocityTheory.PGsh.Up
