-- Prove2me | solution 1 for PaddedDescent.F.Mark.placeE_eq_placeM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:15:21.621581+00:00
-- url     : https://prove2.me/submissions/907eedc6-b9c4-484e-b695-360e7e23daa8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
import Theorems.Thm_PaddedDescent_F_Mark_Layers_drop_eq_cons
import Theorems.Thm_PaddedDescent_F_Mark_Layers_getLastD_drop
import Theorems.Thm_PaddedDescent_F_Mark_trunc_sub_trunc
import Theorems.Thm_PaddedDescent_F_Mark_placeM_eq_placeAt
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
theorem _root_.solution {n w : ℕ} {ev : List Fml → ℤ} {Ls : List Fml} (C : Cl) (h0 : Ls ≠ []) (hI : Inv n w Ls)
    (hl : (Ls.getLastD []).length ≤ w)
    (hev : ∀ i, i + 1 < Ls.length → ev (Ls.drop i) = trunc n w (Ls.drop i) ∧
      ev ((C :: Ls.getD i []) :: Ls.drop (i + 1)) = trunc n w ((C :: Ls.getD i []) :: Ls.drop (i + 1))) :
    placeE ev w Ls C = placeM n w C Ls := by
  rw [placeE, placeM_eq_placeAt C h0 (dropE ev w Ls C)]
  intro i hi
  obtain ⟨e1, e2⟩ := hev i hi
  have hd := drop_eq_cons (show i < Ls.length by omega)
  have hd' := drop_eq_cons hi
  have hIi : Inv n w (Ls.getD i [] :: Ls.getD (i + 1) [] :: Ls.drop (i + 1 + 1)) := by
    rw [← hd', ← hd]; exact hI.drop i
  have hli : ((Ls.getD i [] :: Ls.getD (i + 1) [] :: Ls.drop (i + 1 + 1)).getLastD []).length ≤ w := by
    rw [← hd', ← hd, getLastD_drop (by omega)]; exact hl
  have hB := trunc_sub_trunc C hIi hli
  rw [← hd'] at hB
  rw [dropE, e1, e2, decide_eq_true_iff, hd, hB, dropC, List.flatten_cons, List.length_append]
  rw [show (Ls.getD i []).length + (Ls.drop (i + 1)).flatten.length + 3 = (Ls.drop (i + 1)).flatten.length + (Ls.getD i []).length + 3 by omega]
  norm_cast
end PaddedDescent.F.Mark
