-- Prove2me | solution 1 for Paper.eStar_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:22:46.379791+00:00
-- url     : https://prove2.me/submissions/051bfdc3-8869-41b1-ba04-d9b83caa9e48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Networks
import Definitions.Def_Paper_SecLevel_Grid
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_Paper_SecLevel_Recursion

set_option autoImplicit false
section
section
open Paper
open Groundwork Groundwork.Prog
namespace Paper
theorem _root_.solution {e : ℝ} (h0 : 0 ≤ e) (h : ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e) : eStar ≤ e :=
  csInf_le ⟨0, fun _ he => he.1⟩ ⟨h0, h⟩
end Paper
