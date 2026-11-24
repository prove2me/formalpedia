-- Prove2me | solution 1 for ULHC.far_link
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:16:45.666845+00:00
-- url     : https://prove2.me/submissions/42e3cc62-a8de-484b-bea7-8d0f9b7e0c47

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Theorems.Thm_ULHC_single_pat
import Theorems.Thm_ULHC_endCell_mk
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_end_same
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_front
import Theorems.Thm_ULHC_mem_flipCol_out
import Theorems.Thm_ULHC_mem_flip_off
import Theorems.Thm_ULHC_mid_touch
import Theorems.Thm_ULHC_strip_even_rel
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
include hF hT hk hcell hpat hsep
namespace ULHC
theorem _root_.solution {d : Pt} {tf : Side} (hd : IsCell V d)
    (hb : back d tf ∈ flipCol F c s (k + 2)) (hf : front d tf ∈ flipCol F c s (k + 2))
    (hl1 : lat1 d tf ∉ flipCol F c s (k + 2)) (hl2 : lat2 d tf ∉ flipCol F c s (k + 2))
    (hn : ¬ Conn (flipCol F c s (k + 2)) (back1 d tf) (front1 d tf))
    (hfar : ∀ j < k + 2, ∀ x ∈ cellE d, x ∉ cellE (cellJ c s j)) :
    CR2 V F ⟨c, s, k + 2⟩ ⟨d, tf, 1⟩ := by
  have hsame : ∀ x ∈ cellE d, (x ∈ flipCol F c s (k + 2) ↔ x ∈ F) := fun x hx =>
    mem_flipCol_out (fun j hj => hfar j hj x hx)
  have hfl : ∀ x ∈ cellE d, (x ∈ flip F (cellJ c s (k + 1)) ↔ x ∈ F) := fun x hx =>
    mem_flip_off (hfar (k + 1) (by omega) x hx)
  have mem : ∀ x, x = back d tf ∨ x = front d tf ∨ x = lat1 d tf ∨ x = lat2 d tf → x ∈ cellE d := by
    intro x hx; rw [cellE_frame d tf]; rcases hx with rfl | rfl | rfl | rfl <;> simp
  have bF := (hsame _ (mem _ (Or.inl rfl))).1 hb
  have fF := (hsame _ (mem _ (Or.inr (Or.inl rfl)))).1 hf
  have l1F : lat1 d tf ∉ F := fun h => hl1 ((hsame _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))).2 h)
  have l2F : lat2 d tf ∉ F := fun h => hl2 ((hsame _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))).2 h)
  have hm1 : ¬ IsMid c s k (back1 d tf) := fun hm => by
    obtain ⟨i, hi, hxi⟩ := mid_touch hF hpat hcell hm bF ((ends_back d tf).inc_iff _ |>.2 (Or.inl rfl))
    exact hfar i hi _ (mem _ (Or.inl rfl)) hxi
  have hm2 : ¬ IsMid c s k (front1 d tf) := fun hm => by
    obtain ⟨i, hi, hxi⟩ := mid_touch hF hpat hcell hm fF ((ends_front d tf).inc_iff _ |>.2 (Or.inl rfl))
    exact hfar i hi _ (mem _ (Or.inr (Or.inl rfl))) hxi
  obtain ⟨F1, hF1, _, _, _, _, hodd⟩ :=
    strip_even_rel k hk F hF hcell hpat hsep (end_same hT hk hcell hpat)
  unfold CR2
  dsimp only
  refine ⟨by omega, by omega, le_rfl, ?_, fun j hj => ?_, fun j hj i hi x hx => ?_, fun j hj => ?_,
    fun h => by simp at h, by rw [show k + 2 - 2 = k by omega]; exact hm1,
    by rw [show k + 2 - 2 = k by omega]; exact hm2, hT d hd tf bF fF l1F l2F, ?_⟩
  · rw [endCell_mk]
    exact single_pat ((hfl _ (mem _ (Or.inl rfl))).2 bF)
      (fun h => l1F ((hfl _ (mem _ (Or.inr (Or.inr (Or.inl rfl))))).1 h))
      (fun h => l2F ((hfl _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))).1 h))
      ((hfl _ (mem _ (Or.inr (Or.inl rfl)))).2 fF)
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero]; exact hd
  · simp only at hj hi
    obtain rfl : j = 0 := by omega
    rw [cellJ_zero] at hx
    exact hfar i (by omega) x hx
  · obtain rfl : j = 0 := by omega
    rw [cellJ_zero, endCell_mk]
    intro h
    exact hfar (k + 1) (by omega) _ (mem _ (Or.inl rfl)) (by rw [← h]; exact mem _ (Or.inl rfl))
  · rw [endCell_mk]
    intro h
    exact hn ((hodd _ _ hm1 hm2).2 (Or.inl (hF1 ▸ h)))
end ULHC
