-- Prove2me | solution 1 for PaddedDescent.F.Lists.length_flatMap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:20:39.806207+00:00
-- url     : https://prove2.me/submissions/ee1354a9-5972-43cb-9306-96f1e75b6bd5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_LenList
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Lists
open Groundwork
namespace PaddedDescent.F.Lists
theorem _root_.solution {α β : Type*} (w : List α) (e : α → List β) (c : ℕ) (h : ∀ a ∈ w, (e a).length ≤ c) :
    (w.flatMap e).length ≤ w.length * c := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have h1 := h a (by simp)
    have h2 := ih fun b hb => h b (by simp [hb])
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith
end PaddedDescent.F.Lists
