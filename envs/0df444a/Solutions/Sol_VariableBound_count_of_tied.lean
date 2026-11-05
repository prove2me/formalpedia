-- Prove2me | solution 1 for VariableBound.count_of_tied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:11.2032+00:00
-- url     : https://prove2.me/submissions/53b9edf8-944d-421b-8c2d-6874061bc147

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
theorem _root_.solution {A : List Bool × U → List Bool} {e : List Bool → ℕ} {rn rm : ℕ → ℝ} (h : TiedOut A e id rn rm) : SatM.CountUniformInRate rn rm :=
  let ⟨M, C, hfin, _, h1, h2, h3⟩ := h
  ⟨M, C, hfin, h1, h2, h3⟩
end VariableBound
