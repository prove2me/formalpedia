-- Prove2me | solution 1 for VariableBound.Correct.planAtD_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:28:51.949126+00:00
-- url     : https://prove2.me/submissions/c8f6e3c8-d293-4c5c-a30c-0421b8748a44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open VariableBound VariableBound.Correct
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.Net
namespace VariableBound.Correct
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) {k n s v : ℕ} {i : Idx} (h : planAtD S k n i s = some v) :
    (s0U k ≤ s ∧ 2 ^ betaU k s ≤ n + 1 ∧ 29 * LD (2 ^ betaU k s) + 19 ≤ n) ∧ v = needD S k i n s := by
  unfold planAtD at h
  split_ifs at h with hc
  obtain ⟨v', h1, h2⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h2 with hc2
  obtain ⟨u, h3, h4⟩ := Option.map_eq_some_iff.1 h1
  have hu := hS.needC_eq _ _ _ h3
  refine ⟨hc, ?_⟩
  rw [← Option.some.inj h2, ← h4, hu]
  rfl
end VariableBound.Correct
