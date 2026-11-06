-- Prove2me | solution 1 for VariableBound.Net.Tuples.sum_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:37:10.454846+00:00
-- url     : https://prove2.me/submissions/f0a11d51-904e-44e9-ab3f-3d51869a0fef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_Net_Tuples
import Theorems.Thm_VariableBound_Net_Tuples_card_kP_zero
import Theorems.Thm_VariableBound_Net_Tuples_card_kP_one
import Theorems.Thm_VariableBound_Net_Tuples_back_sl
import Theorems.Thm_VariableBound_Net_Tuples_sl_zero_back
import Theorems.Thm_VariableBound_Net_Tuples_sl_one_back
import Theorems.Thm_VariableBound_Net_Tuples_mem_tup
import Theorems.Thm_VariableBound_Net_Tuples_sl_subset_Vof
import Theorems.Thm_VariableBound_Net_Tuples_sl_one_subset
import Theorems.Thm_VariableBound_Net_Tuples_back_subset_vset
import Theorems.Thm_VariableBound_Net_Tuples_vset_subset
import Theorems.Thm_VariableBound_Net_Tuples_wt_eq
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}
open Classical
namespace VariableBound.Net.Tuples
theorem _root_.solution (hW : WfD k n D) (nb M : ℕ) (fl : Bool) (σ : Fin n → Bool) :
    (∑ P ∈ (vset (Mark.ext σ) D).powerset, if Lim nb M D fl P then wt D fl P else 0) =
      ∑ S₀ ∈ (Vof D.1 σ).powerset with (if fl = true then #S₀ ≤ nb else #S₀ = nb + 1),
        (bif fl then (-1) ^ #S₀ else 1) * ∑ S ∈ AppVariables.tup (Vof (n := n) D.1) (chks D) M σ, ∏ j, ParityChecks.sig #(S j) := by
  rw [← sum_filter]
  simp_rw [mul_sum]
  rw [← sum_product']
  refine sum_nbij' (fun P => (sl D 0 0 P, fun j : Fin (chks D).length => sl D 1 j.val P)) (fun x => back D x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 hP
    have hv := mem_powerset.1 h1
    have hr := hv.trans (vset_subset _ D)
    rw [card_kP_zero hW hr] at h2
    rw [card_kP_one hW hr] at h3
    exact mem_product.2 ⟨mem_filter.2 ⟨mem_powerset.2 (sl_subset_Vof hv 0 0), h2⟩,
      mem_tup.2 ⟨fun j => subset_inter (sl_one_subset hr j.val) (sl_subset_Vof hv 1 j.val), h3⟩⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_product.1 hx
    obtain ⟨h3, h4⟩ := mem_filter.1 h1
    obtain ⟨h5, h6⟩ := mem_tup.1 h2
    have hv : back D x.1 x.2 ⊆ vset (Mark.ext σ) D := back_subset_vset (mem_powerset.1 h3) fun j => (h5 j).trans inter_subset_right
    have hr := hv.trans (vset_subset _ D)
    refine mem_filter.2 ⟨mem_powerset.2 hv, ?_, ?_⟩
    · rw [card_kP_zero hW hr, sl_zero_back]
      exact h4
    · rw [card_kP_one hW hr]
      refine le_trans (le_of_eq (sum_congr rfl fun j _ => ?_)) h6
      rw [sl_one_back _ _ j ((h5 j).trans inter_subset_left)]
  · intro P hP
    exact back_sl hW ((mem_powerset.1 (mem_filter.1 hP).1).trans (vset_subset _ D))
  · intro x hx
    obtain ⟨_, h2⟩ := mem_product.1 hx
    obtain ⟨h5, _⟩ := mem_tup.1 h2
    exact Prod.ext (sl_zero_back _ _) (funext fun j => sl_one_back _ _ j ((h5 j).trans inter_subset_left))
  · intro P hP
    exact wt_eq hW ((mem_powerset.1 (mem_filter.1 hP).1).trans (vset_subset _ D)) fl
end VariableBound.Net.Tuples
