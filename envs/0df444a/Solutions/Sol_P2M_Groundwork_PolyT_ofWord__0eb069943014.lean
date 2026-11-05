-- Prove2me | solution 1 for P2M_Groundwork_PolyT_ofWord__0eb069943014
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:26:28.855189+00:00
-- url     : https://prove2.me/submissions/53110ec0-6ae1-43a3-a12c-d0a9784ffcc6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_Groundwork_PolyT_congr

section
namespace Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
private theorem foldr_bit (w : List Bool) : w.foldr Nat.bit 0 = ofWord w := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [List.foldr_cons, ih, ofWord, Nat.bit_val, Nat.add_comm]
end Groundwork.PolyT
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {w : α → List Bool} (hw : PolyT w) :
    PolyT (fun x => ofWord (w x)) :=
  (ofBits hw).congr fun x => foldr_bit (w x)
end Groundwork.PolyT
