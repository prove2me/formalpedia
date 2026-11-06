-- Prove2me | solution 1 for VariableBound.ArithNeed.lowerDR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:41:54.348064+00:00
-- url     : https://prove2.me/submissions/8f97be93-788a-4787-96b8-96627c479c73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithNeed
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.ArithNeed
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL UniformInK VariableBound.Net
namespace VariableBound.ArithNeed
theorem _root_.solution (hL : StLowerD) {k K n s C₀ : ℕ} (hβ1 : 1 ≤ betaU k s) (hkβ : k ≤ betaU k s) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    (K : ℝ) * ((3 * K ^ 8 * K.size : ℕ) : ℝ) ≤ 3 * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((PbD K n (2 ^ betaU k s) * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) ≤ ((3 * GD C₀ : ℕ) : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ betaU k s)) (PbD K n (2 ^ betaU k s)) : ℕ) : ℝ) ≤
      ((19 + 140 * k + GD C₀ : ℕ) : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    ((3 * K ^ 8 * PbD K n (2 ^ betaU k s) : ℕ) : ℝ) ≤ (GD C₀ : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((18 * K ^ 16 : ℕ) : ℝ) ≤ 18 * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (K : ℝ) ^ 2 ≤ ((WofU (betaU k s) K : ℕ) : ℝ) * n ∧
    (K : ℝ) * ((C₀ : ℝ) * (K : ℝ) ^ 2 * ((5 * (17 * C₀ * K.size) + 16 : ℕ) : ℝ)) ≤ ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ betaU k s)) : ℕ) : ℝ) ≤ ((18 * (4 + 17 * C₀) : ℕ) : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ betaU k s) + 1) * (Nat.size (2 ^ betaU k s * n) + 2) + 8) + 2 + (betaU k s + 5 * k + 10 + (k + 3) * n.size) : ℕ) : ℝ) ≤
      ((10 + 34 * C₀ : ℕ) : ℝ) * (((WofU (betaU k s) K : ℕ) : ℝ) * n) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := hL (betaU k s) k K n C₀ hβ1 hkβ hK hn17 hlt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast o1
  · exact_mod_cast o2
  · exact_mod_cast o3
  · exact_mod_cast o4
  · exact_mod_cast o5
  · exact_mod_cast o6
  · exact_mod_cast o7
  · exact_mod_cast o8
  · exact_mod_cast o9
end VariableBound.ArithNeed
