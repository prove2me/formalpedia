-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.charThm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:49.1529+00:00
-- url     : https://prove2.me/submissions/ccc0e02f-0175-47fb-98d7-f9018e233f81

import Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
import Definitions.Def_ReciprocityTheory_DualLattices_UpBrChar
import Theorems.Thm_ReciprocityTheory_PGsh_Up_char_ind
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_isDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] [IsDomain R]
variable {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : CharStatement := by
  intro C _ v R _ _ hv g N M c hc hspan
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  obtain ⟨ι, hinj, h⟩ := char_ind hv M c hc hspan g le_rfl
  exact ⟨ι, hinj, fun s hs => h s hs⟩
end ReciprocityTheory.PGsh.Up
