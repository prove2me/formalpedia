-- Prove2me | solution 1 for QueryMachines.Bridge.solverOfMachineLevelsFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:53:16.098213+00:00
-- url     : https://prove2.me/submissions/416478c8-0f22-4a8e-9ddd-353557a29e7f

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
import Theorems.Thm_QueryMachines_Bridge_Proof_solver_right
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_QueryMachines_Bridge_Proof_length_unary
import Theorems.Thm_QueryMachines_Bridge_Proof_one_le_logK


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels Proof
namespace QueryMachines.Bridge
theorem _root_.solution : SolverOfMachineLevelsFrom := by
  intro hPlug hRight hVal hBits hCut hSuff hSmall hPoly hPick M _ K e C₀ kf num hSol hL hk hN
  obtain ⟨hpp, hpick⟩ := hPick K e C₀ kf hL hk
  have hcut := (hCut K e C₀ num hL hN).2
  have hKi : ∀ l : ℕ, (solverOfMachine M num C₀).K (unary l, unary (K l)) = K l := fun l => length_unary _
  refine ⟨hPoly M num C₀ hN.1, ⟨{
    idx := fun l => (unary l, unary (K l))
    K_two := fun l => by rw [hKi]; exact hL.K_two l
    K_lt := fun l => by rw [hKi, hKi]; exact hL.K_lt l
    K_le := fun l => by
      rw [hKi, hKi]
      exact (hL.K_le l).trans (Nat.pow_le_pow_right (by have := hL.K_two l; omega) (by omega))
    e_le := fun l => (hcut l).2.2.2.1
    e_ge := fun l => by
      rw [hKi]
      have h1 := one_le_logK hL l
      refine le_trans (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 (by omega : C₀ ≤ 2 * C₀ + 1))) ((hL.e_ge l).trans (hcut l).2.1)
    correct := by
      rintro pad _ lam B ⟨lu, T⟩ ⟨l, rfl⟩ hlam hW hpad
      rw [hKi] at hW ⊢
      exact solver_right hPlug hRight hVal hBits hCut hSuff hSol hL hN pad l lam B lu T hlam hW hpad
    rate := fun l lam B hlam hB => by
      rw [hKi]
      exact hSmall K e C₀ num hL hN l lam B hlam hB
    pick := pickOf kf (K 0)
    pick_poly := hpp
    pick_idx := fun b => (hpick b).1
    pick_le := fun b h => by
      rw [hKi] at h
      rw [(hpick b).1, hKi]
      exact (hpick b).2.1 h
    pick_max := fun b => by rw [hKi]; exact (hpick b).2.2 }, fun _ => rfl, hKi, rfl⟩⟩
end QueryMachines.Bridge
