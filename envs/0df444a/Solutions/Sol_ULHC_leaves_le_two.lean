-- Prove2me | solution 1 for ULHC.leaves_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:38.4155+00:00
-- url     : https://prove2.me/submissions/c918342a-ca2f-452c-bc45-8d108fa873b7

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
import Theorems.Thm_ULHC_deg_erase
import Theorems.Thm_ULHC_Inside_mono
import Theorems.Thm_ULHC_conn_map
import Theorems.Thm_ULHC_one_le_deg
import Theorems.Thm_ULHC_exists_inc_of_deg
import Theorems.Thm_ULHC_inc_unique
import Theorems.Thm_ULHC_other_inc
import Theorems.Thm_ULHC_other_ne
import Theorems.Thm_ULHC_adj_inc
import Theorems.Thm_ULHC_inc_two
import Theorems.Thm_ULHC_Adj_mono
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_mono
import Theorems.Thm_ULHC_Conn_of_adj
import Theorems.Thm_ULHC_Conn_refl
import Theorems.Thm_ULHC_Conn_symm
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
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} :
    ∀ (n : ℕ) (F : Finset Edge), F.card = n → Inside V F → (∀ y, deg F y ≤ 2) →
      ∀ x, (V.filter (fun y => Conn F x y ∧ deg F y = 1)).card ≤ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hn hV hdeg x
  by_contra hlt
  push Not at hlt
  set L := V.filter (fun y => Conn F x y ∧ deg F y = 1)
  obtain ⟨y0, hy0⟩ : L.Nonempty := Finset.card_pos.1 (by omega)
  simp only [L, Finset.mem_filter] at hy0
  obtain ⟨hy0V, hxy0, hd0⟩ := hy0
  obtain ⟨e0, he0, hi0⟩ := exists_inc_of_deg (F := F) (y := y0) (by omega)
  set z := other e0 y0
  have hzi : e0.p = z ∨ e0.q = z := other_inc
  have hzne : z ≠ y0 := other_ne hi0
  have uniq0 : ∀ e ∈ F, (e.p = y0 ∨ e.q = y0) → e = e0 := fun e he hy =>
    inc_unique hd0 he0 hi0 he hy
  have hz1 : 1 ≤ deg F z := one_le_deg he0 hzi
  rcases (show deg F z = 1 ∨ deg F z = 2 by have := hdeg z; omega) with hdz | hdz
  · -- The class of `y0` is `{y0, z}`.
    have uniqz : ∀ e ∈ F, (e.p = z ∨ e.q = z) → e = e0 := fun e he hy =>
      inc_unique hdz he0 hzi he hy
    have small : ∀ w, Conn F y0 w → w = y0 ∨ w = z := by
      intro w hw
      induction hw with
      | refl => exact Or.inl rfl
      | tail _ huv ihw =>
        rename_i u v
        obtain ⟨e, he, hu, hv, _⟩ := adj_inc huv
        have hee : e = e0 := by
          rcases ihw with rfl | rfl
          · exact uniq0 e he hu
          · exact uniqz e he hu
        subst hee
        exact inc_two hi0 hzi hzne.symm hv
    have : L ⊆ {y0, z} := by
      intro y hy
      simp only [L, Finset.mem_filter] at hy
      have := small y (hxy0.symm.trans hy.2.1)
      simp only [Finset.mem_insert, Finset.mem_singleton]; exact this
    have h1 := Finset.card_le_card this
    have h2 : ({y0, z} : Finset Pt).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega
  · -- Remove the pendant edge and use the induction hypothesis at `z`.
    set F0 := F.erase e0 with hF0
    have hcard : F0.card < n := by
      have h1 : F0.card = F.card - 1 := Finset.card_erase_of_mem he0
      have h2 : 0 < F.card := Finset.card_pos.2 ⟨e0, he0⟩
      omega
    have hV0 : Inside V F0 := hV.mono (Finset.erase_subset _ _)
    have hdeg0 : ∀ y, deg F0 y ≤ 2 := by
      intro y; have h1 := deg_erase he0 y; rw [← hF0] at h1; have := hdeg y; omega
    have IH := ih _ hcard F0 rfl hV0 hdeg0 z
    set L0 := V.filter (fun y => Conn F0 z y ∧ deg F0 y = 1)
    have hzL0 : z ∈ L0 := by
      simp only [L0, Finset.mem_filter]
      refine ⟨?_, Conn.refl _ _, ?_⟩
      · rcases hzi with h | h <;> rw [← h]
        · exact (hV e0 he0).1
        · exact (hV e0 he0).2
      · have h1 := deg_erase he0 z; rw [← hF0, if_pos hzi] at h1; omega
    let f : Pt → Pt := fun w => if w = y0 then z else w
    have hf : ∀ u v, Adj F u v → Conn F0 (f u) (f v) := by
      intro u v huv
      obtain ⟨e, he, h'⟩ := huv
      have hu : e.p = u ∨ e.q = u := by
        rcases h' with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Or.inl h1
        · exact Or.inr h2
      have hv : e.p = v ∨ e.q = v := by
        rcases h' with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr h2
        · exact Or.inl h1
      by_cases hee : e = e0
      · subst hee
        have fz : ∀ w, (e.p = w ∨ e.q = w) → f w = z := by
          intro w hw
          rcases inc_two hi0 hzi hzne.symm hw with h | h
          · simp only [f, if_pos h]
          · subst h; simp only [f, if_neg hzne]
        rw [fz u hu, fz v hv]; exact Conn.refl _ _
      · have hu0 : u ≠ y0 := fun h => hee (uniq0 e he (h ▸ hu))
        have hv0 : v ≠ y0 := fun h => hee (uniq0 e he (h ▸ hv))
        simp only [f, if_neg hu0, if_neg hv0]
        exact Conn.of_adj ⟨e, Finset.mem_erase.2 ⟨hee, he⟩, h'⟩
    have sub : L.erase y0 ⊆ L0.erase z := by
      intro y hy
      simp only [Finset.mem_erase, L, Finset.mem_filter] at hy
      obtain ⟨hyy0, hyV, hxy, hdy⟩ := hy
      have hyz : y ≠ z := by intro h; subst h; omega
      have hni : ¬ (e0.p = y ∨ e0.q = y) := by
        rintro (h | h)
        · rcases hi0 with h0 | h0
          · exact hyy0 (h.symm.trans h0)
          · rcases hzi with h1 | h1
            · exact hyz (h.symm.trans h1)
            · exact hzne (h1.symm.trans h0)
        · rcases hi0 with h0 | h0
          · rcases hzi with h1 | h1
            · exact hzne (h1.symm.trans h0)
            · exact hyz (h.symm.trans h1)
          · exact hyy0 (h.symm.trans h0)
      simp only [Finset.mem_erase, L0, Finset.mem_filter]
      refine ⟨hyz, hyV, ?_, ?_⟩
      · have := conn_map f hf (hxy0.symm.trans hxy)
        simp only [f, if_pos rfl, if_neg hyy0] at this
        exact this
      · have h1 := deg_erase he0 y; rw [← hF0, if_neg hni] at h1; omega
    have c1 := Finset.card_le_card sub
    have hy0L : y0 ∈ L := by
      simp only [L, Finset.mem_filter]; exact ⟨hy0V, hxy0, hd0⟩
    rw [Finset.card_erase_of_mem hy0L, Finset.card_erase_of_mem hzL0] at c1
    omega
end ULHC
