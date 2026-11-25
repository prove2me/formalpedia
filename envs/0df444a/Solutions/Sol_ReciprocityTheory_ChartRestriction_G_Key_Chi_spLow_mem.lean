-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spLow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:27:32.338733+00:00
-- url     : https://prove2.me/submissions/fc6d68a7-d901-46b0-83f1-8fcc508e73c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_J_mem_spH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spLow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {S : Matrix (Fin g) (Fin g) ℤ} (hS : S.IsSymm) : spLow S ∈ spH g := by

  have hS' : (-S).IsSymm := by
    unfold Matrix.IsSymm at hS ⊢
    rw [Matrix.transpose_neg, hS]
  rw [spLow_eq]
  exact mul_mem (mul_mem J_mem_spH (spTransl_mem hS')) (mul_mem (mul_mem J_mem_spH J_mem_spH) J_mem_spH)
end ReciprocityTheory.ChartRestriction.G.Key.Chi
