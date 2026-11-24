-- Prove2me | solution 1 for Psi.noDescent_false_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:28:57.734919+00:00
-- url     : https://prove2.me/submissions/fd37f442-b256-4a15-9f4b-398076067ade

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_cLead0_take
import Theorems.Thm_Psi_cLead1_take
import Theorems.Thm_Psi_cLead0_drop
import Theorems.Thm_Psi_cLead1_drop
import Theorems.Thm_Psi_noDescent_sorted

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution {w : List Bool} (hw : noDescent w = false) :
    w = List.replicate (cLead0 w) false
          ++ List.replicate (cLead1 (w.drop (cLead0 w))) true
          ++ false :: (w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)
        ∧ 1 ≤ cLead1 (w.drop (cLead0 w)) := by
  set a := cLead0 w with ha
  set v := w.drop a with hv
  set b := cLead1 v with hb
  have hwv : w = List.replicate a false ++ v := by
    conv_lhs => rw [← List.take_append_drop a w]
    rw [cLead0_take w]
  have hvb : v = List.replicate b true ++ v.drop b := by
    conv_lhs => rw [← List.take_append_drop b v]
    rw [cLead1_take v]
  have hv_head : v.head? ≠ some false := by have := cLead0_drop w; rwa [← hv] at this
  have hvd_head : (v.drop b).head? ≠ some true := cLead1_drop v
  clear_value a v b
  cases hd : v.drop b with
  | nil =>
    exfalso
    have hvr : v = List.replicate b true := by rw [hvb, hd, List.append_nil]
    rw [hwv, hvr, noDescent_sorted] at hw
    exact absurd hw (by simp)
  | cons c cs =>
    have hc : c = false := by
      rcases c with _ | _
      · rfl
      · exact absurd (by rw [hd]; rfl) hvd_head
    subst hc
    have hcs : v.drop (b + 1) = cs := by
      have hx : v.drop (b + 1) = (v.drop b).drop 1 := by rw [List.drop_drop]
      rw [hx, hd]; rfl
    have hb1 : 1 ≤ b := by
      by_contra hb0
      have hb00 : b = 0 := by omega
      rw [hb00] at hd; simp at hd
      rw [hd] at hv_head; simp at hv_head
    refine ⟨?_, hb1⟩
    conv_lhs => rw [hwv, hvb, hd]
    rw [hcs]
    simp [List.append_assoc]
end Psi
