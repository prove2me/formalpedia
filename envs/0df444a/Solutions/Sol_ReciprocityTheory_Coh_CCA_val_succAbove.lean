-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.val_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:32.493091+00:00
-- url     : https://prove2.me/submissions/13389d0b-fffc-44f7-a7b2-9aa4f46f237a

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {X V W Z : Type u} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    (i.succAbove k : ℕ) = if (k : ℕ) < i then (k : ℕ) else k + 1 := by
  by_cases h : (k : ℕ) < i
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.mpr h), Fin.coe_castSucc]
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.mpr (Nat.le_of_not_lt h)),
      Fin.val_succ]
end ReciprocityTheory.Coh.CCA
