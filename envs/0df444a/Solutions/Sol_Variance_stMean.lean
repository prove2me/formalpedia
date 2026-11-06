-- Prove2me | solution 1 for Variance.stMean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:36:54.929217+00:00
-- url     : https://prove2.me/submissions/e2bff23a-b52d-4089-b16b-5ab19e66c9c5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Cov
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Var
import Theorems.Thm_Variance_stSoMean
import Theorems.Thm_Variance_stPairProb
import Theorems.Thm_Variance_stYIsSum


set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks
namespace Variance
theorem _root_.solution : StMean := stSoMean stYIsSum stPairProb
end Variance
