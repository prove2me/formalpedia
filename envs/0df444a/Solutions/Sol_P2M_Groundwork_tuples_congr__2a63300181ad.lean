-- Prove2me | solution 1 for P2M_Groundwork_tuples_congr__2a63300181ad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:05:41.894943+00:00
-- url     : https://prove2.me/submissions/75b12eaf-e9c3-4f96-8c71-9aadc6b00e23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal

set_option autoImplicit false
section
open Groundwork
open Finset
namespace Groundwork
theorem _root_.solution {ι X : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] {T T' : ι → Finset X}
    (d : X) (h : ∀ i, P i → T i = T' i) : tuples P T d = tuples P T' d := by
  unfold tuples
  congr 1
  funext i
  split_ifs with hi
  · exact h i hi
  · rfl
end Groundwork
