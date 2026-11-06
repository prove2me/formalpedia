-- Prove2me | solution 1 for OccurM.everyWrapperCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:01:12.192638+00:00
-- url     : https://prove2.me/submissions/a66c1115-e992-4e27-9ff8-4fbbdef59a67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_OccurM_Wrapper
import Theorems.Thm_OccurM_wrapper_counts
import Theorems.Thm_OccurM_one_le_length_encC


set_option autoImplicit false
section
section
open OccurM
open Groundwork Turing MainTheoremForms ClausesOccur
open Sat3 (CNF)
namespace OccurM
theorem _root_.solution : EveryWrapperCounts := fun _ h0 h1 _ hpre _ _ hM _ _ hW =>
  ⟨_, wrapper_counts h0 h1 (fun k _ φ => encC k φ) hpre one_le_length_encC hM hW⟩
end OccurM
