-- Prove2me | solution 1 for Supersequence.project_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:57:58.639303+00:00
-- url     : https://prove2.me/submissions/49db8863-5da7-47aa-9466-5069a99eea52

import Std
import Definitions.Def_Frequency

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
namespace Supersequence
theorem _root_.solution (x : α) (a b : List α) :
    project x (a ++ b) = project x a ++ project x b := filter_append a b
end Supersequence
