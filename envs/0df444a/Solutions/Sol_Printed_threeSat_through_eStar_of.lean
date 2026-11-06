-- Prove2me | solution 1 for Printed.threeSat_through_eStar_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:14:12.703203+00:00
-- url     : https://prove2.me/submissions/932fa439-b5eb-48b5-af2a-dfc603fec0bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Proof
import Theorems.Thm_Eight_decidesInSteps_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_steps_to_time


set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Eight Eight.SecNetworks Paper QueryMachines
namespace Printed
theorem _root_.solution (hEta : StEveryEta) (hEn : Enumerate.StEnumeration) (hPN : StProofNamed) : Sat3.ThmEveryDelta := by
  intro δ hδ
  have hδ₀ : 0 < min (δ / 2) 1 := lt_min (by linarith) one_pos
  obtain ⟨M, τ, hM, hE⟩ := hEn (min (δ / 2) 1 / 3) (by linarith)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hδ' : 0 < min (δ / 2) 1 / (3 * (M : ℝ)) := div_pos hδ₀ (by linarith)
  obtain ⟨K, hK, _, _, Mq, Cc, hp, hA⟩ := hEta (min (δ / 2) 1 / (3 * (M : ℝ)) / 12) (by linarith) ⌈72 / (min (δ / 2) 1 / (3 * (M : ℝ)))⌉₊
  have hKδ : 72 / (min (δ / 2) 1 / (3 * (M : ℝ))) ≤ K := (Nat.le_ceil _).trans (by exact_mod_cast hK)
  obtain ⟨h1, h2⟩ := hPN (min (δ / 2) 1) M τ K Mq Cc hδ₀ (min_le_right _ _) hM hE hKδ hp hA
  exact steps_to_time hδ _ h1 (Eight.decidesInSteps_mono h2 (min_le_left _ _))
end Printed
