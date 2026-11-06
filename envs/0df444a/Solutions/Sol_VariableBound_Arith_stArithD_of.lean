-- Prove2me | solution 1 for VariableBound.Arith.stArithD_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:57:04.488196+00:00
-- url     : https://prove2.me/submissions/462195eb-5192-42f7-8c6b-983201f2341b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_UniformInK_Top_ArithTop
import Definitions.Def_UniformInK_Top_ArithTop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithTop
import Theorems.Thm_VariableBound_Arith_planAtD_le
import Theorems.Thm_ClauseBound_TopN_Arith_eq_replicate
import Theorems.Thm_ClauseBound_TopN_Arith_root17_spec
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open VariableBound VariableBound.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.Arith
namespace VariableBound.Arith
theorem _root_.solution (hN : StNeedD) (hP : StPlanLeD) (hPN : StPlanNeedD) (hM : StMasterU) (hDL : StDLogU) (h6 : StSixU) (hB : StBetaU) : StArithD := by
  intro Idx _ S e C₀ Q hS slU C h1 h2
  refine ⟨AexpD C₀, BkD C C₀, fun k n hk hn => ?_⟩
  by_cases hBk : BkD C C₀ * k ^ 2 ≤ Nat.log 2 n
  swap
  · exact Or.inr (not_le.1 hBk)
  left
  obtain ⟨hr1, hr2⟩ := root17_spec n
  have hK0 : S.K (Q.idx 0) ≤ (root17 n).length := by
    by_contra h
    have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 17
    exact absurd (h'.trans hn) (not_le.2 hr2)
  have hle := Q.pick_le _ hK0
  have hmax := Q.pick_max (root17 n)
  have hidx := Q.pick_idx (root17 n)
  have hu := eq_replicate (Q.pick (root17 n)).1
  obtain ⟨l, hl⟩ : ∃ l, l = (Q.pick (root17 n)).1.length := ⟨_, rfl⟩
  rw [← hl] at hu hidx hmax ⊢
  rw [hidx] at hle ⊢
  rw [hu]
  have g1 := h1 l
  have g2 := h2 l
  obtain ⟨s, hs⟩ : ∃ s, s = (slU (List.replicate l ())).length := ⟨_, rfl⟩
  rw [← hs] at g1 g2 ⊢
  have hK2 := Q.K_two l
  have hn17 : S.K (Q.idx l) ^ 17 ≤ n := (Nat.pow_le_pow_left hle 17).trans hr1
  have hlt : n < S.K (Q.idx l) ^ (17 * C₀) := by
    calc n < ((root17 n).length + 1) ^ 17 := hr2
      _ ≤ (S.K (Q.idx l) ^ C₀) ^ 17 := Nat.pow_le_pow_left ((Nat.succ_le_of_lt hmax).trans (Q.K_le _)) 17
      _ = S.K (Q.idx l) ^ (17 * C₀) := by rw [← pow_mul, mul_comm]
  exact planAtD_le hN hP hPN hM hDL h6 hB hS (Q.idx l) hk hK2 hn17 hlt (Q.e_le l) g1 (Q.e_ge l) g2 (Q.rate l) hBk
end VariableBound.Arith
