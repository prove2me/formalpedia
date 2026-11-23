-- Prove2me | solution 1 for congruence_same_eqvcls_imp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:40.488851+00:00
-- url     : https://prove2.me/submissions/ac2505f5-9ac8-49aa-a953-dc508dda3479

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Congruences_Basic

set_option autoImplicit true
open Function Set Stream'
open Classical
variable {A : Type}
variable {c : Congruence A}
theorem _root_.solution {s : c.QuotType} {u u' : List A}
    (h : u ∈ c.EqvCls s) (h' : u' ∈ c.EqvCls s) : c.eq u u' := by
  apply Quotient.exact
  simp [Congruence.EqvCls] at h h'
  exact h.trans h'.symm
