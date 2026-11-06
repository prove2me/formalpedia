-- Prove2me | solution 1 for Sat3Graph.askSized_polyTimeSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:23:59.250479+00:00
-- url     : https://prove2.me/submissions/32d65583-8ff1-4759-be0b-42edc2754a10

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SizeCircuit_SizedCert
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Walk
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Cert
import Theorems.Thm_Eight_Width_widthP_polyT
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_SizeCircuit_withGamma_polyT
attribute [local fun_prop] Groundwork.PolyT.comp



set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit Complement SplitSat
namespace Sat3Graph
theorem _root_.solution {gates : ℕ → ℕ → List CircuitLowerBound.GateD} (hC : CertGates gates) {D : StepMachine (List Unit × Fml) Bool} (hD : PolyTimeSteps D) :
    PolyTimeSteps (askSized gates D) := by
  obtain ⟨h⟩ := hD
  exact ⟨IsPolyT.mapIn (M := D) (f := fun p => widthP (withGamma gates p)) (PolyT.comp widthP_polyT (withGamma_polyT hC))⟩
end Sat3Graph
