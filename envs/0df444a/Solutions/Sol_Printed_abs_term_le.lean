-- Prove2me | solution 1 for Printed.abs_term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:30:28.174059+00:00
-- url     : https://prove2.me/submissions/bb48507f-40a6-430c-9fde-f5ece5580dc0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Printed_card_factors_le
import Theorems.Thm_Printed_abs_prod_le_pow
import Theorems.Thm_Printed_one_le_two_pow_sub
import Theorems.Thm_ClauseBound_Grid_abs_prod_le_pow
import Theorems.Thm_Eight_SecNetworks_length_thetaAt
import Theorems.Thm_Eight_ViaGrouping_Table_isPaperNetwork
import Theorems.Thm_Groundwork_Network_merge_c
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_mem_tuples
import Theorems.Thm_Groundwork_mem_words
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
variable {C : Type} [HasSize C] {g K : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
namespace Printed
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ) (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L)
    (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) {z : Fin g → List Bool} (hz : z ∈ tuples (fun a => Paper.grouping hK0 x a = γ) N.S []) :
    |(∏ a with Paper.grouping hK0 x a = γ, N.W a (z a)) *
        (∏ p ∈ pairs (Fin g) with Paper.grouping hK0 x p.1 = γ ∧ Paper.grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
        ∏ p : Fin g × Fin g with Paper.grouping hK0 x p.1 = γ ∧ Paper.grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np.toPaperNetwork c hK0 x Θ p.1 p.2)| ≤ (2 ^ B - 1) ^ g ^ 2 := by
  rw [mem_tuples] at hz
  have hm1 := one_le_two_pow_sub h.is.B_pos
  have hm0 : (0 : ℤ) ≤ 2 ^ B - 1 := by linarith
  have hL' : ∀ γ γ' : Fin K, γ ≠ γ' → (N.toPaperNetwork.merge (Paper.grouping hK0 x) [] []).c γ γ' ≤ L := fun γ γ' hne => by
    rw [Groundwork.Network.merge_c]
    exact hY γ γ' hne
  rw [abs_mul, abs_mul]
  refine (mul_le_mul (mul_le_mul (abs_prod_le_pow _ _ (2 ^ B - 1) ?_) (abs_prod_le_pow _ _ (2 ^ B - 1) ?_) (abs_nonneg _) (pow_nonneg hm0 _)) (abs_prod_le_pow _ _ (2 ^ B - 1) ?_) (abs_nonneg _)
    (mul_nonneg (pow_nonneg hm0 _) (pow_nonneg hm0 _))).trans ?_
  · exact fun a ha => Int.le_sub_one_of_lt (h.is.ii_W a _ ((hz a).1 (mem_filter.1 ha).2))
  · intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := mem_filter.1 hp
    have hlt : p.1 < p.2 := (mem_filter.1 hp1).2
    exact Int.le_sub_one_of_lt (h.is.ii_Ψ _ _ hlt.ne _ ((hz _).1 hp2) _ ((hz _).1 hp3))
  · intro p hp
    obtain ⟨hp1, hp2⟩ := (mem_filter.1 hp).2
    have hne : Paper.grouping hK0 x p.1 ≠ Paper.grouping hK0 x p.2 := fun e => hp2 (e ▸ hp1)
    have hlen : (thetaAt Np.toPaperNetwork c hK0 x Θ p.1 p.2).length = N.c p.1 p.2 := length_thetaAt Np.toPaperNetwork hK0 (Table.isPaperNetwork h) x L hL' Θ hne (hΘ _ hp2)
    exact Int.le_sub_one_of_lt (h.is.ii_f _ _ (fun e : p.1 = p.2 => hne (by rw [e])) _ ((hz _).1 hp1) _ (mem_words.2 hlen))
  · rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hm1 (card_factors_le _ γ)
end Printed
