-- Prove2me | solution 1 for ULHC.split_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:24:08.055842+00:00
-- url     : https://prove2.me/submissions/7b6d9aec-6650-4781-8393-f7a3b02160c4

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_flip_alt_count
import Theorems.Thm_ULHC_flip_flip_comm
import Theorems.Thm_ULHC_mem_flip_off
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_mkLat_cellE
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hG : Deg2 V G) {u v : Pt} {s tf : Side} (hu : IsCell V u) (hv : IsCell V v)
    (lu1 : lat1 u s ∈ G) (lu2 : lat2 u s ∈ G) (bu : back u s ∉ G) (fu : front u s ∉ G)
    (lv1 : lat1 v tf ∈ G) (lv2 : lat2 v tf ∈ G) (bv : back v tf ∉ G) (fv : front v tf ∉ G)
    (hsu : Conn G (back1 u s) (back2 u s)) (hsv : Conn G (back1 v tf) (back2 v tf))
    (hdisj : ∀ e, e ∈ cellE u → e ∉ cellE v) :
    Conn (flip G u) (back1 v tf) (back2 v tf) ↔ Conn (flip G v) (back1 u s) (back2 u s) := by
  have hdisj' : ∀ e, e ∈ cellE v → e ∉ cellE u := fun e h1 h2 => hdisj e h2 h1
  have mv : ∀ e, e ∈ cellE v → (e ∈ flip G u ↔ e ∈ G) := fun e he => mem_flip_off (hdisj' e he)
  have mu : ∀ e, e ∈ cellE u → (e ∈ flip G v ↔ e ∈ G) := fun e he => mem_flip_off (hdisj e he)
  have sv : ∀ e, e = lat1 v tf ∨ e = lat2 v tf ∨ e = back v tf ∨ e = front v tf → e ∈ cellE v := by
    intro e he; rw [cellE_frame v tf]; rcases he with rfl | rfl | rfl | rfl <;> simp
  have su : ∀ e, e = lat1 u s ∨ e = lat2 u s ∨ e = back u s ∨ e = front u s → e ∈ cellE u := by
    intro e he; rw [cellE_frame u s]; rcases he with rfl | rfl | rfl | rfl <;> simp
  have hGu : Deg2 V (flip G u) := hG.flip (mkLat u s) hu (mkLat_cellE u s) lu1 lu2 bu fu
  have hGv : Deg2 V (flip G v) := hG.flip (mkLat v tf) hv (mkLat_cellE v tf) lv1 lv2 bv fv
  have cu := (flip_alt_count hG hu lu1 lu2 bu fu).1 hsu
  have cv := (flip_alt_count hG hv lv1 lv2 bv fv).1 hsv
  have A := flip_alt_count hGu hv ((mv _ (sv _ (Or.inl rfl))).2 lv1)
    ((mv _ (sv _ (Or.inr (Or.inl rfl)))).2 lv2)
    (fun h => bv ((mv _ (sv _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
    (fun h => fv ((mv _ (sv _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
  have B := flip_alt_count hGv hu ((mu _ (su _ (Or.inl rfl))).2 lu1)
    ((mu _ (su _ (Or.inr (Or.inl rfl)))).2 lu2)
    (fun h => bu ((mu _ (su _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
    (fun h => fu ((mu _ (su _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
  rw [flip_flip_comm] at A
  constructor
  · intro h
    by_contra h'
    have := A.1 h; have := B.2 h'; omega
  · intro h
    by_contra h'
    have := A.2 h'; have := B.1 h; omega
end ULHC
