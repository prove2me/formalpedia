-- Prove2me | solution 1 for ULHC.TF.walk_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:52:57.166404+00:00
-- url     : https://prove2.me/submissions/f833179c-e5ba-4bea-b6ed-2f1ddaca524e

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_ends_iff
import Theorems.Thm_ULHC_TF_other_black
import Theorems.Thm_ULHC_TF_layer_sub_succ
import Theorems.Thm_ULHC_TF_deg_erase_end
import Theorems.Thm_ULHC_TF_deg_erase_off
import Theorems.Thm_ULHC_TF_deg_insert_end
import Theorems.Thm_ULHC_TF_deg_insert_off
import Theorems.Thm_ULHC_TF_pred_some
import Theorems.Thm_ULHC_TF_pred_ne_none
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Inside_mono
import Theorems.Thm_ULHC_other_ne
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
theorem _root_.solution {V : Finset Pt} {F0 : Finset Edge} (hF0 : Good V F0) (k : ℕ) :
    ∀ v F, WInv V F0 k v F →
      Good V (walk V F0 (layersBelow V F0 k) v F) ∧
        (walk V F0 (layersBelow V F0 k) v F).card = F0.card + 1 := by
  induction k with
  | zero =>
    rintro v F ⟨hv, hin, hle, -, hb, -, -⟩
    show Good V F ∧ F.card = F0.card + 1
    simp only [layer, mem_filter] at hv
    obtain ⟨-, hvb, hvd⟩ := hv
    obtain ⟨hd, hc⟩ := hb hvb
    refine ⟨⟨hin, fun z => ?_⟩, hc⟩
    by_cases hz : z = v
    · subst hz; omega
    · exact hle z hz
  | succ k ih =>
    rintro v F ⟨hv, hin, hle, hw, hb, hdeg, hfl⟩
    have hsub : layer V F0 k ⊆ layer V F0 (k + 1) := layer_sub_succ
    have hfl' : ∀ e, (e ∈ F ↔ e ∈ F0) ∨ e.p ∉ layer V F0 k ∨ e.q ∉ layer V F0 k := by
      intro e
      rcases hfl e with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl fun h' => h (hsub h'))
      · exact Or.inr (Or.inr fun h' => h (hsub h'))
    by_cases hvk : v ∈ layer V F0 k
    · rw [layersBelow, walk, if_pos hvk]
      exact ih v F ⟨hvk, hin, hle, hw, hb, fun z hz => hdeg z (hsub hz), hfl'⟩
    rw [layersBelow, walk, if_neg hvk]
    rcases hp : pred V F0 (layer V F0 k) v with _ | e
    · exact absurd hp (pred_ne_none hv hvk)
    simp only
    obtain ⟨hev, hE, hu, hbk, hwk⟩ := pred_some hp
    have hends := ends_iff hev
    have huv : other e v ≠ v := other_ne hev
    have hcol := other_black hev
    have hu' : other e v ∈ layer V F0 (k + 1) := hsub hu
    have heF : e ∈ F ↔ e ∈ F0 := by
      rcases hfl e with h | h | h
      · exact h
      · exfalso; apply h
        rcases (hends e.p).1 (Or.inl rfl) with h' | h' <;> rw [h']
        exacts [hv, hu']
      · exfalso; apply h
        rcases (hends e.q).1 (Or.inr rfl) with h' | h' <;> rw [h']
        exacts [hv, hu']
    -- Points other than `v` and `other e v` keep their degree.
    --
    have hoff : ∀ z, z ≠ v → z ≠ other e v → ¬ (e.p = z ∨ e.q = z) := by
      intro z h1 h2 h
      rcases (hends z).1 h with h | h
      exacts [h1 h, h2 h]
    have hfl2 : ∀ G : Finset Edge, (∀ f, f ≠ e → (f ∈ G ↔ f ∈ F)) →
        ∀ f, (f ∈ G ↔ f ∈ F0) ∨ f.p ∉ layer V F0 k ∨ f.q ∉ layer V F0 k := by
      intro G hG f
      by_cases hfe : f = e
      · subst hfe
        rcases hev with h | h
        · exact Or.inr (Or.inl (h ▸ hvk))
        · exact Or.inr (Or.inr (h ▸ hvk))
      · rcases hfl' f with h | h
        · exact Or.inl ((hG f hfe).trans h)
        · exact Or.inr h
    by_cases hvb : Black v
    · -- Black `v`: erase the `F0`-edge `e`, moving to the white point `other e v`.
      --
      rw [if_pos hvb]
      have heF' : e ∈ F := heF.2 (hbk hvb)
      obtain ⟨hdv, hc⟩ := hb hvb
      have hub : ¬ Black (other e v) := fun h => hcol.1 h hvb
      apply ih
      refine ⟨hu, hin.mono (erase_subset _ _), ?_, ?_, ?_, ?_, ?_⟩
      · intro z hz
        by_cases hzv : z = v
        · subst hzv
          have := deg_erase_end heF' hev
          have := hF0.2 z
          omega
        · rw [deg_erase_off heF' (hoff z hzv hz)]; exact hle z hzv
      · intro _
        have h1 := deg_erase_end heF' ((hends _).2 (Or.inr rfl))
        have h2 := hdeg _ hu' huv
        have h3 := hF0.2 (other e v)
        have h4 := card_erase_of_mem heF'
        omega
      · intro h; exact absurd h hub
      · intro z hz hzu
        have hzv : z ≠ v := fun h => hvk (h ▸ hz)
        rw [deg_erase_off heF' (hoff z hzv hzu)]
        exact hdeg z (hsub hz) hzv
      · apply hfl2
        intro f hf
        rw [mem_erase]
        exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
    · -- White `v`: insert the non-`F0` edge `e`, moving to the black point `other e v`.
      --
      rw [if_neg hvb]
      have heF' : e ∉ F := fun h => hwk hvb (heF.1 h)
      obtain ⟨hdv, hc⟩ := hw hvb
      have hub : Black (other e v) := hcol.2 hvb
      apply ih
      refine ⟨hu, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro f hf
        rcases mem_insert.1 hf with h | h
        · subst h; exact hE
        · exact hin f h
      · intro z hz
        by_cases hzv : z = v
        · subst hzv
          rw [deg_insert_end heF' hev]
          omega
        · rw [deg_insert_off heF' (hoff z hzv hz)]; exact hle z hzv
      · intro h; exact absurd hub h
      · intro _
        rw [deg_insert_end heF' ((hends _).2 (Or.inr rfl)), hdeg _ hu' huv,
          card_insert_of_notMem heF', hc]
        exact ⟨rfl, rfl⟩
      · intro z hz hzu
        have hzv : z ≠ v := fun h => hvk (h ▸ hz)
        rw [deg_insert_off heF' (hoff z hzv hzu)]
        exact hdeg z (hsub hz) hzv
      · apply hfl2
        intro f hf
        rw [mem_insert]
        exact ⟨fun h => h.resolve_left hf, fun h => Or.inr h⟩
end ULHC.TF
