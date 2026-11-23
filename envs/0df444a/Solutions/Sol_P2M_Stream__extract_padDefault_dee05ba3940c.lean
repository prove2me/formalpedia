-- Prove2me | solution 1 for P2M_Stream__extract_padDefault_dee05ba3940c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:15:18.565215+00:00
-- url     : https://prove2.me/submissions/7852c20c-14aa-470f-b28e-7f97bfb59da4

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
import Theorems.Thm_P2M_Stream__extract_eq_ofFn_8231fd1645c4

set_option autoImplicit true
open Function Set Option Stream'
open Stream'
variable {X : Type*}
namespace Stream'
theorem _root_.solution [Inhabited X] {xl : List X} :
    xl.padDefault.extract 0 xl.length = xl := by
  simp [List.padDefault, extract_eq_ofFn]
end Stream'
