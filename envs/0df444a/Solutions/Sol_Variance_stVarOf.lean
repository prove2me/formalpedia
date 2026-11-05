-- Prove2me | solution 1 for Variance.stVarOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:07:51.579599+00:00
-- url     : https://prove2.me/submissions/dcff943d-0a6e-449a-ae5c-c71660ff2c42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Cov
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Var
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks
namespace Variance
theorem _root_.solution : StVarOf := by
  intro hV hD hO hH g K P c hs hP γ γ' hne
  rw [hV g K c γ γ' hne]
  refine (hH g P c hs hP (cov γ γ') ((K : ℤ) ^ 4 * (K : ℤ) ^ g) (by positivity) (hD g K γ γ') (hO g K γ γ')).trans (le_of_eq ?_)
  push_cast
  ring
end Variance
