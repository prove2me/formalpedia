-- Prove2me | solution 1 for TDLC.Syntax.erase_elaborate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:27.389336+00:00
-- url     : https://prove2.me/submissions/7a9a62a0-6656-497c-9095-38e5e8944535

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
import Theorems.Thm_TDLC_Syntax_Lookup_index_variable
import Theorems.Thm_TDLC_Path_parity_ap
import Theorems.Thm_TDLC_Path_parity_concat
import Theorems.Thm_TDLC_Path_parity_inv
import Theorems.Thm_TDLC_Path_parity_lEmbed
import Theorems.Thm_TDLC_bxor_false_left
import Theorems.Thm_TDLC_bxor_false_right
import Theorems.Thm_TDLC_bxor_self
attribute [local simp] TDLC.Path.parity_ap
attribute [local simp] TDLC.Path.parity_concat
attribute [local simp] TDLC.Path.parity_inv
attribute [local simp] TDLC.Path.parity_lEmbed
attribute [local simp] TDLC.bxor_false_left
attribute [local simp] TDLC.bxor_false_right
attribute [local simp] TDLC.bxor_self



set_option autoImplicit true
open TDLC TDLC.Syntax
namespace TDLC.Syntax
theorem _root_.solution (h : HasType Γ r a) : erase (elaborate h) = r := by
  induction h with
  | var h => exact congrArg Raw.var h.index_variable
  | app f x ihf ihx => simp only [elaborate, erase, ihf, ihx]
  | lam t ih => exact congrArg (Raw.lam _) ih
end TDLC.Syntax
