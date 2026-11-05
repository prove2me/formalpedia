-- Prove2me | solution 1 for VariableBound.Net.Ev.presents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:57:35.533227+00:00
-- url     : https://prove2.me/submissions/c3a59b72-4e06-45a6-ba4f-028252b7834d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_Ev
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Ev
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg
open ClauseBound.ParityChecks (Vof)
namespace VariableBound.Net.Ev
theorem _root_.solution (hPr : StPresents) (g n : ℕ) (D : Dat) (y : ℕ) (fl : Bool) : netD.toP.Presents (ctx g n D y fl) (netDN g (ctx g n D y fl)) 0 0 := by
  have h := hPr (ctx g n D y fl)
  have e : (ctx g n D y fl).1.1.length = g := List.length_replicate
  rw [e] at h
  exact h
end VariableBound.Net.Ev
