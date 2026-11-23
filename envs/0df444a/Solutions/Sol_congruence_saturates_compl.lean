-- Prove2me | solution 1 for congruence_saturates_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:27.118564+00:00
-- url     : https://prove2.me/submissions/afe8b8a4-31b6-488e-b47e-628fa8561c73

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Congruences_Basic

set_option autoImplicit true
open Function Set Stream'
open Classical
variable {A : Type}
variable {c : Congruence A}
theorem _root_.solution {L : Set (Stream' A)}
    (h_sat : c.Saturates L) : c.Saturates Lᶜ := by
  rintro s t ⟨as, h_as, h_as_c⟩ as' h_as'
  by_contra h_contra
  simp at h_contra
  have h_l : (c.ConcatOmegaLang s t ∩ L).Nonempty := by
    use as' ; simp [h_as', h_contra]
  have := h_sat s t h_l h_as
  contradiction
