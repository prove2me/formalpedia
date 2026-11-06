-- Prove2me | solution 1 for P2M_Eight_ViaGrouping_lvlPsi_netOf__runs_ab9065b5caad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:52:26.641305+00:00
-- url     : https://prove2.me/submissions/cbfb70e9-a675-4b2e-8d86-e9641ef5315e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
import Theorems.Thm_Eight_ViaGrouping_lvlPsi_runs
import Theorems.Thm_Eight_ViaGrouping_lvlPsiSize_le
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_P2M_Eight_Level_netOf__S_6e5e490549e4
import Theorems.Thm_P2M_Eight_Level_netOf__sized_t_6d348568ee7d
import Theorems.Thm_Paper_Achievable_mono
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_nat



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution {C : Type} [HasSize C] {g : ℕ} {tr : Bool} {psi : ℕ → ℕ → PsiQ → ℤ} (hΨ : StPsiOK g tr psi) (lam : C → ℕ) (c : C) {y B : ℕ}
    {Rm : Inst (Fin (g * g)) (List Bool)} (hl : 1 ≤ lam c) (hy : y < (tOf (lam c) + 1) ^ nRect g) (hR : BoundedInst (lam c) B Rm) (a b : Fin (nParts g g tr)) (hab : a ≠ b)
    {z z' : List Bool} (hz : z ∈ (netOfι g tr (lam c) y Rm).S a) (hz' : z' ∈ (netOfι g tr (lam c) y Rm).S b) :
    (ofFun fun x : (C × ℕ) × PsiQ => psi (lam x.1.1) x.1.2 x.2).Runs ((c, y), ((a.val, b.val), (z, z'))) 1 (lvlPsiSize g * (size c + B + lam c))
      ((netOfι g tr (lam c) y Rm).Ψ a b z z') := by
  have hg : nParts g g tr = g := by cases tr <;> rfl
  have htn : tOf (lam c) ≤ lam c := by unfold tOf; omega
  have hrun := lvlPsi_runs psi lam c (hΨ (lam c) y Rm hl hy a b hab z hz z' hz') (lt_of_lt_of_eq a.2 hg) (lt_of_lt_of_eq b.2 hg)
    (mem_words.1 (netOfι_S g tr (lam c) y Rm a ▸ hz)) (mem_words.1 (netOfι_S g tr (lam c) y Rm b ▸ hz')) ((netOfι_sized_t hl g tr y hR).abs_Ψ a b z z' hab)
  refine hrun.mono le_rfl (lvlPsiSize_le g (size c) B (lam c) (size y) _ hl ?_ (Nat.add_le_add_left (Nat.mul_le_mul_left _ htn) _))
  have h1 : y < 2 ^ ((tOf (lam c) + 1) * nRect g) := by
    refine hy.trans_le ?_
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
  have h2 := Nat.size_le.2 h1
  have h3 : (tOf (lam c) + 1) * nRect g ≤ 2 * nRect g * lam c := by
    calc (tOf (lam c) + 1) * nRect g ≤ 2 * lam c * nRect g := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * nRect g * lam c := by ring
  rw [size_nat]
  omega
end Eight.ViaGrouping
