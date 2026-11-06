-- Prove2me | solution 1 for Printed.AchievedBy.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:56:13.844424+00:00
-- url     : https://prove2.me/submissions/3c4d9257-a2f3-472e-8b52-47bf90f8ddfc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Absorb
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
import Definitions.Def_Printed_Achievable
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
namespace Printed
namespace AchievedBy
theorem _root_.solution {M : CliqueMachine} {Cc K : ℕ} {e e₁ : ℝ} (h : AchievedBy M Cc K e) (he : e ≤ e₁) : AchievedBy M Cc K e₁ := fun lam B W hl hB hW => by
  obtain ⟨T, hr, hT⟩ := h lam B W hl hB hW
  refine ⟨T, hr, hT.trans ?_⟩
  gcongr
  norm_num
end AchievedBy
end Printed
