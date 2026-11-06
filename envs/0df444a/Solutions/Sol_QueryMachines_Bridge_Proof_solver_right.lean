-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.solver_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:43:32.390983+00:00
-- url     : https://prove2.me/submissions/a056985d-de19-4fbf-837f-8cc7b4dd89b9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Tables
import Definitions.Def_CountedToPadded_Need
import Definitions.Def_CountedToPadded_Pick
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_Levels
import Theorems.Thm_QueryMachines_Bridge_Proof_bound_mono
import Theorems.Thm_QueryMachines_Bridge_Proof_le_bound
import Theorems.Thm_QueryMachines_Bridge_Proof_size_query_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_ofFun_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_QueryMachines_Bridge_Proof_eq_unary
import Theorems.Thm_QueryMachines_Bridge_Proof_size_entry_le
import Theorems.Thm_QueryMachines_Bridge_Proof_size_le_len_tab
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_QueryMachine_sum_map_const
import Theorems.Thm_QueryMachines_QueryMachine_sum_map_unitCost
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local simp] Groundwork.size_prod



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels
variable {M : QueryMachine TableQuery ℤ (U × U × U) ℤ} [QueryMachine.IsPolyQ M] {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} {num : U × U → ℕ × ℕ}
namespace QueryMachines.Bridge.Proof
theorem _root_.solution (hPlug : StPlug) (hRight : RunForIsRight) (hVal : TablesValue) (hBits : BitsOfTablesFacts) (hCut : CutNumberFacts) (hSuff : NeedSuffices)
    (hSol : Solves M K e C₀) (hL : Levels K e C₀) (hN : NumberBetween K e num) (pad : U) (l lam B : ℕ) (lu : U) (T : Tab) (hlam : 1 ≤ lam) (hW : WFe (K l) lam B (lu, T))
    (hpad : 2 ^ needOf num C₀ ((unary l, unary (K l)), unary lam, unary B) ≤ pad.length) :
    (solverOfMachine M num C₀).run (pad, (unary l, unary (K l)), (lu, T)) = zval (K l) (lu, T) := by
  obtain ⟨hb1, hbe, hbB⟩ := hBits T
  have hB' := hbB (K l) lam B lu hW
  have hlu : lu = unary lam := by rw [eq_unary lu]; exact congrArg unary hW.2
  subst hlu
  obtain ⟨hc0, hc1, -, -, -⟩ := (hCut K e C₀ num hL hN).2 l
  obtain ⟨T₀, S₀, ⟨own, L, hr, hc⟩, hT0, hS0⟩ := hSol l lam (bitsOfTables T) (fun w z => entry T (w, z)) hlam hb1 fun w _ z _ => hbe (w, z)
  have hK2 := hL.K_two l
  -- the bound β and what it covers
  have hβ := bound_mono (K l) C₀ lam hc1 hB'
  have h4 := hSuff K e C₀ num hL hN l lam B hlam
  have hle := le_bound (K := K l) (C₀ := C₀) (lam := lam) (B + 1) hc0.le hL.C₀_pos (by omega) hlam
  have hpad' : (2 : ℝ) ^ needOf num C₀ ((unary l, unary (K l)), unary lam, unary B) ≤ (pad.length : ℝ) := by exact_mod_cast hpad
  generalize bound (cutNumber K num l) (K l) C₀ lam (B + 1) = β at *
  -- the run of the machine with its queries answered from the tables
  have hq : ∀ x ∈ L, ∀ v, tables (K l) lam (fun w z => entry T (w, z)) x = some v → lookup.Runs (T, x) ((fun _ => 1) x) (size T + (K l + 2 * (K l * lam) + 2) + 1) v := by
    intro x _ v hv
    unfold tables at hv
    split at hv
    · rename_i hx
      obtain rfl : entry T x = v := Option.some.inj hv
      have h1 := size_query_le hx.1 hx.2
      have h2 := size_entry_le T x
      have h3 : size (T, x) = size T + size x := size_prod _
      refine (Stepped.ofFun_runs (fun p : Tab × TableQuery => entry p.1 p.2) (T, x)).mono le_rfl (Nat.succ_le_succ (max_le ?_ ?_))
      · rw [h3]; omega
      · exact h2.trans (Nat.le_add_right _ _)
    · cases hv
  have hrun := hPlug _ _ _ _ _ M lookup _ T _ own S₀ _ L _ (fun _ => 1) hr hq
  have hsum1 : (L.map QueryMachine.unitCost).sum = L.length := QueryMachine.sum_map_unitCost L
  have hsum3 : (L.map fun _ : TableQuery => 1 + 2).sum = L.length * (1 + 2) := QueryMachine.sum_map_const L (1 + 2)
  rw [hsum1] at hc
  have hTn : own + (L.map fun _ : TableQuery => 1 + 2).sum ≤ pad.length := by
    rw [hsum3]
    have h5 : ((own + L.length * (1 + 2) : ℕ) : ℝ) ≤ 3 * (T₀ : ℝ) := by
      have : ((own + L.length : ℕ) : ℝ) ≤ T₀ := Nat.cast_le.2 hc
      have h0 : (0 : ℝ) ≤ own := Nat.cast_nonneg _
      push_cast at this ⊢
      linarith
    have h6 : ((own + L.length * (1 + 2) : ℕ) : ℝ) ≤ (pad.length : ℝ) := by
      have : (0 : ℝ) ≤ β := le_trans (by positivity) hle
      linarith
    exact_mod_cast h6
  have hSn : S₀ + (K l + 2 * (K l * lam) + 2) + 2 ≤ pad.length := by
    have hK' : (2 : ℝ) ≤ K l := by exact_mod_cast hK2
    have hl' : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have h7 : ((S₀ + (K l + 2 * (K l * lam) + 2) + 2 : ℕ) : ℝ) ≤ (pad.length : ℝ) := by
      push_cast at hle ⊢
      nlinarith
    exact_mod_cast h7
  have hlen := size_le_len_tab T
  have hres := @hRight _ _ (onTables M) (inferInstanceAs (Enc (OnTablesState M))) (inferInstanceAs (Carried (OnTablesState M))) _ _ _ _ pad (7 * pad.length + 14 * len T + 2) hrun hTn (by omega)
  have hv := hVal (K l) lam T hK2 hlam
  exact (congrArg (fun o : Option ℤ => o.getD 0) hres).trans hv
end QueryMachines.Bridge.Proof
