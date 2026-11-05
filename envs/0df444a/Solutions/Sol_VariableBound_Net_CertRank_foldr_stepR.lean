-- Prove2me | solution 1 for VariableBound.Net.CertRank.foldr_stepR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:34:33.108492+00:00
-- url     : https://prove2.me/submissions/f66e8a20-d35a-401c-a8be-ef3a36240ac2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Rank
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertRank

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Net.CertRank
namespace VariableBound.Net.CertRank
theorem _root_.solution (x : List Bool) : x.foldr stepR ([], 0) = (x, rank x) := by
  induction x with
  | nil => rfl
  | cons b x ih => rw [List.foldr_cons, ih]; rfl
end VariableBound.Net.CertRank
