-- Prove2me | solution 1 for PaddedDescent.F.Top.walk_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:51:52.626636+00:00
-- url     : https://prove2.me/submissions/1e2f0d22-0581-481c-9a25-95b6c0fc39ff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_NSat
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_PaddedDescent_F_Top_walk
import Theorems.Thm_PaddedDescent_F_Top_treeK
import Theorems.Thm_PaddedDescent_F_Top_one_le_tauOf
import Theorems.Thm_PaddedDescent_F_Top_length_markPar
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
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
import Theorems.Thm_PaddedDescent_F_Mark_NSat_cast_nSat_pos_iff
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
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
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)
namespace PaddedDescent.F.Top
theorem _root_.solution (hCount : StCountM) (hLf : StLeaf) (hSched : StSched) (hA : StA) (hAW : StAW) {k n : ℕ} (hk : 1 ≤ k) (hs : s0K k ≤ sOf n)
    (pad : U) (hF : 2 ^ (8 * (n / 2 ^ sOf n + 1)) ≤ pad.length) (ψ : Fml) (hψl : ψ.length ≤ inLen k n)
    (hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    walkF k pad (tauOf (sOf n))
      (fun x => decide (0 < countM k pad ((schedF pad (depthOf (sOf n))).1, (schedF pad (depthOf (sOf n))).2.1) (markPar n (sOf n)) (layersOf (sOf n)) x))
      (rootP ψ) = true ↔ Fml.Sat ψ := by
  obtain ⟨w1, w2, w3, w4⟩ := hAW k n pad.length hk hs hF
  obtain ⟨a1, a2⟩ := hA k n pad.length (leafC (tauOf (sOf n)) k + 2) (by omega) hF w1 w2
  rw [hSched pad _ a2]
  obtain ⟨p1, p2, p3, p4⟩ := length_markPar n (sOf n)
  obtain ⟨b1, b2, b3, b4⟩ := treeK hLf (one_le_tauOf (sOf n)) ψ hψl hψne
    (fun x => decide (0 < countM k pad (schedL (depthOf (sOf n)), List.replicate (Kseq (depthOf (sOf n))) ()) (markPar n (sOf n))
      (layersOf (sOf n)) x))
    (fun x hx hW ho => by
      rw [decide_eq_true_eq, hCount k pad _ (markPar n (sOf n)) _ _ _ x (by rw [p1, p3, p4]; exact a1) (by rw [p1, p2]) (by rw [p1]; exact hW) ho hx,
        p1]
      exact Mark.NSat.cast_nSat_pos_iff fun C hC => (hW x (by simp) C hC).2.2)
  rw [walk k pad _ _ _ _ b1 (by omega) fun i => (b3 i).trans w4]
  exact b4
end PaddedDescent.F.Top
