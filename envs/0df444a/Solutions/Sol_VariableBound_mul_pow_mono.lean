-- Prove2me | solution 1 for VariableBound.mul_pow_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:09.77557+00:00
-- url     : https://prove2.me/submissions/b1e65738-c4d7-41cf-9c01-388476620571

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_TiedDefs
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_VariableBound_Printed_Tied

set_option autoImplicit false
section
section
open VariableBound
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK UniformInK.End VariableBound.Decide
namespace VariableBound
theorem _root_.solution {q C y : ℕ} (h : q ≤ C) (hy : 1 ≤ y) : q * y ^ q ≤ C * y ^ C :=
  Nat.mul_le_mul h (Nat.pow_le_pow_right hy h)
end VariableBound
