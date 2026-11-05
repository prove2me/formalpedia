-- Prove2me | solution 1 for Wrap.frontEnd_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:10:57.046509+00:00
-- url     : https://prove2.me/submissions/fac20c9f-2537-415b-9f60-b0d79cc7baac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_FrontEnd
import Theorems.Thm_Wrap_encUnary_toN
import Theorems.Thm_Wrap_toN_pad4
import Theorems.Thm_Groundwork_Decode_dec_enc
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_takeWhile
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.takeWhile



set_option autoImplicit false
section
section
open Wrap
open Groundwork Groundwork.Decode
namespace Wrap
theorem _root_.solution {n : ℕ} {φ : Sat3.CNF n} (hφ : ∀ C ∈ φ, C.length ≤ 3) : frontEnd (Sat3.enc φ) = MainTheoremForms.encC 3 (pad4 φ) := by
  have h1 : ((Sat3.enc φ).takeWhile id).length = n := congrArg Prod.fst (dec_enc hφ)
  rw [frontEnd, slotBits, h1, dec_enc hφ, ← toN_pad4, encUnary_toN]
end Wrap
