-- Prove2me | solution 1 for PES.esIndep_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:08:22.460015+00:00
-- url     : https://prove2.me/submissions/decc1cbe-7925-477c-b6cc-924435dccb33

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Stable_LTSI
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Prime_LTSI
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_indep_iff_concurrent
attribute [local simp] PES.enables_iff



set_option autoImplicit true
variable {L : Type*}
open PES
variable (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent
namespace PES
theorem _root_.solution {c c₁ c₂ : Conf es} {a b : L} :
    ConfFamily.esIndep es.toFamily c a c₁ b c₂ ↔ esIndep es c a c₁ b c₂ := by
  constructor
  · rintro ⟨e₁, e₂, hind, f₁, f₂, l₁, l₂, t₁, t₂⟩
    have h₁ := (PES.enables_iff es).mp hind.2.1
    have h₂ := (PES.enables_iff es).mp hind.2.2.1
    exact ⟨e₁, e₂, h₁, h₂, f₁, f₂, l₁, l₂, t₁, t₂,
      (PES.indep_iff_concurrent es h₁ h₂ f₁ f₂).mp hind⟩
  · rintro ⟨e₁, e₂, h₁, h₂, f₁, f₂, l₁, l₂, t₁, t₂, hconc⟩
    exact ⟨e₁, e₂, (PES.indep_iff_concurrent es h₁ h₂ f₁ f₂).mpr hconc,
      f₁, f₂, l₁, l₂, t₁, t₂⟩
end PES
