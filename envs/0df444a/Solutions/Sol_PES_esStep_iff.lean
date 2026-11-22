-- Prove2me | solution 1 for PES.esStep_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:08:22.012066+00:00
-- url     : https://prove2.me/submissions/864be686-efc9-43f5-989b-7a42a9949a2e

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Stable_LTSI
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Prime_LTSI
import Theorems.Thm_PES_enables_iff
attribute [local simp] PES.enables_iff



set_option autoImplicit true
variable {L : Type*}
open PES
variable (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent
namespace PES
theorem _root_.solution {c₁ c₂ : Conf es} {a : L} :
    ConfFamily.esStep es.toFamily c₁ a c₂ ↔ esStep es c₁ a c₂ := by
  constructor
  · rintro ⟨e, hen, hfr, hlbl, htgt⟩
    exact ⟨e, (PES.enables_iff es).mp hen, hfr, hlbl, htgt⟩
  · rintro ⟨e, hen, hfr, hlbl, htgt⟩
    exact ⟨e, (PES.enables_iff es).mpr hen, hfr, hlbl, htgt⟩
end PES
