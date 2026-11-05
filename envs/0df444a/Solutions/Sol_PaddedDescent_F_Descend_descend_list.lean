-- Prove2me | solution 1 for PaddedDescent.F.Descend.descend_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:37:44.244545+00:00
-- url     : https://prove2.me/submissions/400ba8a1-5dc9-49a5-9324-6f547abb1990

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_F_Descend
import Theorems.Thm_PaddedDescent_F_stBrute
import Theorems.Thm_PaddedDescent_F_Fits_head
import Theorems.Thm_Groundwork_BitCut_expand
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_PaddedDescent_F_Lists_len_list_le__7630c2814a7f
import Theorems.Thm_PaddedDescent_F_Lists_length_flatMap_le
import Theorems.Thm_PaddedDescent_F_Lists_sum_map_flatMap
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork Groundwork.Prog Finset Lists
open Descend
namespace PaddedDescent.F
namespace Descend
theorem _root_.solution (h3 : StT3b) (hE : StE) {pad : U} : ∀ (sched : List Lvl) {Kup Λ B cnt : ℕ} (w : List PInst),
    Chain Kup sched → Fits pad.length Kup Λ B cnt sched → w.length ≤ cnt → (∀ I ∈ w, WF Kup Λ B I) →
    ((sched.foldl (fun w L => cap pad [] (w.flatMap (expand pad L))) w).map (bruteF pad 256)).sum = (w.map (zval Kup)).sum
  | [], Kup, Λ, B, cnt, w, hC, hF, _, hw => by
    have hK : Kup = 256 := hC
    subst hK
    rw [List.foldl_nil]
    refine congrArg List.sum (List.map_congr_left fun I hI => stBrute pad 256 I (le_trans ?_ hF.2))
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (hw I hI).lam_le)
  | L :: r, Kup, Λ, B, cnt, w, hC, hF, hc, hw => by
    obtain ⟨hK, h2, h8, hC'⟩ := hC
    obtain ⟨-, hB, hF'⟩ := hF
    subst hK
    have hE' := fun I (hI : I ∈ w) => hE pad L Λ B I h2 h8 (hw I hI) hB
    have hlen : (w.flatMap (expand pad L)).length ≤ cnt * (Λ + 1) ^ nRect L.2.length :=
      (length_flatMap_le w _ _ fun I hI => (hE' I hI).2.2).trans (Nat.mul_le_mul_right _ hc)
    have hWF : ∀ J ∈ w.flatMap (expand pad L),
        WF L.1.length (lamNext L.1.length L.2.length Λ) (bNext L.1.length L.2.length Λ B) J := by
      intro J hJ
      obtain ⟨I, hI, hJ'⟩ := List.mem_flatMap.1 hJ
      exact (hE' I hI).2.1 J hJ'
    have hfit : len (w.flatMap (expand pad L)) ≤ pad.length :=
      (len_list_le' _ _ hlen fun J hJ => h3 _ _ _ J (hWF J hJ)).trans hF'.head
    rw [List.foldl_cons, cap_eq hfit, solution h3 hE r _ hC' hF' hlen hWF, sum_map_flatMap]
    exact congrArg List.sum (List.map_congr_left fun I hI => (hE' I hI).1)
end Descend
end PaddedDescent.F
