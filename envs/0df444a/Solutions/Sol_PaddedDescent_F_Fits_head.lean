-- Prove2me | solution 1 for PaddedDescent.F.Fits.head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:49:13.539417+00:00
-- url     : https://prove2.me/submissions/89a1c698-4f5c-4965-b602-55983ff1ed0a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_F_Descend

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork Groundwork.Prog Finset Lists
open Descend
namespace PaddedDescent.F
namespace Fits
theorem _root_.solution {F : ℕ} : ∀ {sched : List Lvl} {Kup Λ B cnt : ℕ}, Fits F Kup Λ B cnt sched → cnt * instLen Kup Λ B + 2 ≤ F
  | [], _, _, _, _, h => h.1
  | _ :: _, _, _, _, _, h => h.1
end Fits
end PaddedDescent.F
