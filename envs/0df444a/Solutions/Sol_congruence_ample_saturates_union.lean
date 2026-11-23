-- Prove2me | solution 1 for congruence_ample_saturates_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:32.101717+00:00
-- url     : https://prove2.me/submissions/ebee20d5-6753-49ae-9623-49d185a1a7ee

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Congruences_Basic

set_option autoImplicit true
open Function Set Stream'
open Classical
variable {A : Type}
variable {c : Congruence A}
theorem _root_.solution {L : Set (Stream' A)}
    (h_amp : c.Ample) (h_sat : c.Saturates L) :
    L =  ⋃ s, ⋃ t, if (c.ConcatOmegaLang s t ∩ L).Nonempty then c.ConcatOmegaLang s t else ∅ := by
  ext as ; simp ; constructor
  · intro h_l
    obtain ⟨s, t, h_st⟩ := h_amp as
    use s, t ; simp [h_st]
    use as ; simp [h_st, h_l]
  · rintro ⟨s, t, h_ne, h_as⟩
    exact h_sat s t h_ne h_as
