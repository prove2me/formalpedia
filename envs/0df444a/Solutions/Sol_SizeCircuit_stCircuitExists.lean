-- Prove2me | solution 1 for SizeCircuit.stCircuitExists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:54.459905+00:00
-- url     : https://prove2.me/submissions/8ba684d0-21c4-4bd0-a872-98bb22c644cf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_Circuit
import Definitions.Def_SizeCircuit_Cert
import Definitions.Def_SizeCircuit_Sized
import Definitions.Def_SizeCircuit_SizedCert
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Main
import Theorems.Thm_SizeCircuit_certGates_sizeGates
import Theorems.Thm_SizeCircuit_testsSize_sizeGates


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight
namespace SizeCircuit
theorem _root_.solution : StCircuitExists := ⟨sizeGates, 6, testsSize_sizeGates, certGates_sizeGates⟩
end SizeCircuit
