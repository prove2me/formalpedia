-- Prove2me | solution 1 for P2M_CircuitLowerBound_stENP__of_10b343dee6a6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:27:57.600194+00:00
-- url     : https://prove2.me/submissions/7cec5357-50c6-4bfe-bc10-2171190dab7f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_ENP_Round
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Restart
import Theorems.Thm_P2M_CircuitLowerBound_stENP__of_vars_86a2b2596c60
import Theorems.Thm_CircuitLowerBound_stVars


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork PaddedDescent Turing
open Restart
namespace CircuitLowerBound
theorem _root_.solution (h1 : StCertSched) (h2 : StCertTabF) (h3 : StFlip) : StENP' := stENP'_of_vars h1 h2 h3 stVars
end CircuitLowerBound
