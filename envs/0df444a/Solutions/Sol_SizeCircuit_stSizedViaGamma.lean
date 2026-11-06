-- Prove2me | solution 1 for SizeCircuit.stSizedViaGamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:58.003953+00:00
-- url     : https://prove2.me/submissions/5adb6a43-c099-4b65-802d-1c4e26be54a8

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
import Theorems.Thm_SizeCircuit_stSizedFromEngine
import Theorems.Thm_SizeCircuit_certGates_sizeGates
import Theorems.Thm_SizeCircuit_testsSize_sizeGates


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight
namespace SizeCircuit
theorem _root_.solution : StSizedViaGamma := by
  intro hEng w δ hδ
  obtain ⟨E, -, -, -, -, -, -, hP, c', h⟩ := stSizedFromEngine hEng sizeGates 6 testsSize_sizeGates certGates_sizeGates w δ hδ
  exact ⟨sizedBy sizeGates E, hP, c', h⟩
end SizeCircuit
