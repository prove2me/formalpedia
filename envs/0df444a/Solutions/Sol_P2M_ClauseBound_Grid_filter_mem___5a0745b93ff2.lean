-- Prove2me | solution 1 for P2M_ClauseBound_Grid_filter_mem___5a0745b93ff2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:43:47.574212+00:00
-- url     : https://prove2.me/submissions/c29a2d03-bb76-4095-880e-4d522d75dfdc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_ClauseBound_Grid_Expand

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution : (univ.filter fun ω => ω ∈ Ω ρ γ) = Ω ρ γ := by
  ext ω; simp
end ClauseBound.Grid
