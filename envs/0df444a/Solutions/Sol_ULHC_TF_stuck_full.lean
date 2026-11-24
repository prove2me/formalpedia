-- Prove2me | solution 1 for ULHC.TF.stuck_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:57:25.277533+00:00
-- url     : https://prove2.me/submissions/a2213729-b093-4577-8db8-d20ad45ce397

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_ends_iff
import Theorems.Thm_ULHC_TF_other_black
import Theorems.Thm_ULHC_TF_mem_nbr
import Theorems.Thm_ULHC_TF_layer_mono
import Theorems.Thm_ULHC_TF_layer_sub
import Theorems.Thm_ULHC_TF_layer_closed
import Theorems.Thm_ULHC_TF_sum_deg
import Theorems.Thm_ULHC_TF_no_edge_black
import Theorems.Thm_ULHC_TF_no_edge_white
import Theorems.Thm_ULHC_TF_augStep_none
import Theorems.Thm_ULHC_TF_all_two
import Theorems.Thm_ULHC_TF_sum_deg_black
import Theorems.Thm_ULHC_TF_sum_deg_white
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F G : Finset Edge} (hF : Good V F)
    (hst : augStep V F = none) (hG : Deg2 V G) : ∀ z ∈ V, deg F z = 2 := by
  classical
  set R := layer V F V.card with hR
  set SB := R.filter Black
  set SW := R.filter (fun z => ¬ Black z)
  have hRV : R ⊆ V := layer_sub _
  have hSBb : ∀ z ∈ SB, Black z := fun z hz => (mem_filter.1 hz).2
  have hSWw : ∀ z ∈ SW, ¬ Black z := fun z hz => (mem_filter.1 hz).2
  have hSWfull : ∀ z ∈ SW, deg F z = 2 := by
    intro z hz
    obtain ⟨hzR, hzb⟩ := mem_filter.1 hz
    have := augStep_none hst hzR hzb
    have := hF.2 z
    omega
  have hSWG : ∀ z ∈ SW, deg G z = 2 := fun z hz => hG.2 z (hRV (mem_filter.1 hz).1)
  have hSBG : ∀ z ∈ SB, deg G z = 2 := fun z hz => hG.2 z (hRV (mem_filter.1 hz).1)
  -- Touching a set: one end in it.
  --
  let T : Finset Pt → Edge → Prop := fun S e => e.p ∈ S ∨ e.q ∈ S
  have hsumB : ∀ H : Finset Edge, ∑ z ∈ SB, deg H z = (H.filter (T SB)).card :=
    fun H => sum_deg (no_edge_black hSBb) H
  have hsumW : ∀ H : Finset Edge, ∑ z ∈ SW, deg H z = (H.filter (T SW)).card :=
    fun H => sum_deg (no_edge_white hSWw) H
  -- An edge touching `SB` (resp. `SW`) at its end `b`.
  --
  have hend : ∀ (S : Finset Pt) e, T S e → ∃ b ∈ S, e.p = b ∨ e.q = b := by
    rintro S e (h | h)
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h, Or.inr rfl⟩
  have htouch : ∀ (S : Finset Pt) e z, z ∈ S → (e.p = z ∨ e.q = z) → T S e := by
    rintro S e z hz (h | h)
    · exact Or.inl (h ▸ hz)
    · exact Or.inr (h ▸ hz)
  -- Claim 2: an `F`-edge touching `SW` also touches `SB`.
  --
  have hc2 : ∀ e ∈ F, T SW e → T SB e := by
    intro e he hT
    obtain ⟨w, hw, hwe⟩ := hend SW e hT
    obtain ⟨hwR, hwb⟩ := mem_filter.1 hw
    have hfw : Fwd V F w e := ⟨hF.1 e he, fun h => absurd h hwb, fun _ => he⟩
    have hbR : other e w ∈ R := layer_closed hwR (mem_nbr.2 ⟨e, hwe, hfw, rfl⟩)
    have hbb : Black (other e w) := (other_black hwe).2 hwb
    exact htouch SB e _ (mem_filter.2 ⟨hbR, hbb⟩) ((ends_iff hwe _).2 (Or.inr rfl))
  -- Claim 1: a `G`-edge touching `SB` touches `SW` or is an `F`-edge.
  --
  have hc1 : ∀ e ∈ G, T SB e → T SW e ∨ e ∈ F := by
    intro e he hT
    by_cases heF : e ∈ F
    · exact Or.inr heF
    left
    obtain ⟨b, hb, hbe⟩ := hend SB e hT
    obtain ⟨hbR, hbb⟩ := mem_filter.1 hb
    have hfb : Fwd V F b e := ⟨hG.1 e he, fun _ => heF, fun h => absurd hbb h⟩
    have hwR : other e b ∈ R := layer_closed hbR (mem_nbr.2 ⟨e, hbe, hfb, rfl⟩)
    have hww : ¬ Black (other e b) := fun h => (other_black hbe).1 h hbb
    exact htouch SW e _ (mem_filter.2 ⟨hwR, hww⟩) ((ends_iff hbe _).2 (Or.inr rfl))
  -- The edges of `F` touching `SB` but not `SW`.
  --
  set Y := (F.filter (T SB)).filter (fun e => ¬ T SW e)
  have hAF : (F.filter (T SB)).card = 2 * SW.card + Y.card := by
    rw [← card_filter_add_card_filter_not (s := F.filter (T SB)) (T SW)]
    have : (F.filter (T SB)).filter (T SW) = F.filter (T SW) := by
      ext e
      simp only [mem_filter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hc2 e h.1 h.2⟩, h.2⟩⟩
    rw [this, ← hsumW, sum_congr rfl hSWfull, sum_const, smul_eq_mul, mul_comm]
  have hAG : 2 * SB.card ≤ 2 * SW.card + Y.card := by
    have h1 : (G.filter (T SB)).card = 2 * SB.card := by
      rw [← hsumB, sum_congr rfl hSBG, sum_const, smul_eq_mul, mul_comm]
    have h2 : (G.filter (T SW)).card = 2 * SW.card := by
      rw [← hsumW, sum_congr rfl hSWG, sum_const, smul_eq_mul, mul_comm]
    have hsub : G.filter (T SB) ⊆ G.filter (T SW) ∪ Y := by
      intro e he
      obtain ⟨heG, hT⟩ := mem_filter.1 he
      rw [mem_union]
      rcases hc1 e heG hT with h | h
      · exact Or.inl (mem_filter.2 ⟨heG, h⟩)
      · by_cases hW : T SW e
        · exact Or.inl (mem_filter.2 ⟨heG, hW⟩)
        · exact Or.inr (mem_filter.2 ⟨mem_filter.2 ⟨h, hT⟩, hW⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    omega
  have hSBfull : ∀ z ∈ SB, deg F z = 2 :=
    all_two (fun z _ => hF.2 z) (by rw [hsumB, hAF]; exact hAG)
  -- Every black point is full: a deficient one would lie in layer 0, inside `SB`.
  --
  have hBfull : ∀ z ∈ V.filter Black, deg F z = 2 := by
    intro z hz
    obtain ⟨hzV, hzb⟩ := mem_filter.1 hz
    by_contra hne
    have hd : deg F z < 2 := by have := hF.2 z; omega
    have h0 : z ∈ layer V F 0 := mem_filter.2 ⟨hzV, hzb, hd⟩
    have hzR : z ∈ R := layer_mono (Nat.zero_le _) h0
    exact hne (hSBfull z (mem_filter.2 ⟨hzR, hzb⟩))
  -- Colour balance: `|F| = 2 |VB|` and `2 |VB| = |G| = 2 |VW|`.
  --
  have hFB := sum_deg_black hF.1
  have hFW := sum_deg_white hF.1
  have hGB := sum_deg_black hG.1
  have hGW := sum_deg_white hG.1
  rw [sum_congr rfl hBfull, sum_const, smul_eq_mul] at hFB
  rw [sum_congr rfl (fun z hz => hG.2 z (mem_filter.1 hz).1), sum_const, smul_eq_mul] at hGB hGW
  have hWfull : ∀ z ∈ V.filter (fun z => ¬ Black z), deg F z = 2 :=
    all_two (fun z _ => hF.2 z) (by rw [hFW]; omega)
  intro z hz
  by_cases hzb : Black z
  · exact hBfull z (mem_filter.2 ⟨hz, hzb⟩)
  · exact hWfull z (mem_filter.2 ⟨hz, hzb⟩)
end ULHC.TF
