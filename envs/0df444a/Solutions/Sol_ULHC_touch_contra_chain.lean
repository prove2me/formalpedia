-- Prove2me | solution 1 for ULHC.touch_contra_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:34:25.732845+00:00
-- url     : https://prove2.me/submissions/d29e366a-4128-42ee-a2e2-b760834f4925

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_start_not_body
import Theorems.Thm_ULHC_start_not_behind
import Theorems.Thm_ULHC_start_beside1
import Theorems.Thm_ULHC_start_beside2
import Theorems.Thm_ULHC_start_beside_end1
import Theorems.Thm_ULHC_start_beside_end2
import Theorems.Thm_ULHC_start_beyond
import Theorems.Thm_ULHC_start_L0
import Theorems.Thm_ULHC_start_R0
import Theorems.Thm_ULHC_direct_link1
import Theorems.Thm_ULHC_direct_link2
import Theorems.Thm_ULHC_along_not_mem
import Theorems.Thm_ULHC_single3_link
import Theorems.Thm_ULHC_beside_end_farA
import Theorems.Thm_ULHC_beside_end_farB
import Theorems.Thm_ULHC_touch_core
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_swap
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_chain_sig
import Theorems.Thm_ULHC_chain_start
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_nb_nb_opp
import Theorems.Thm_ULHC_side1_down
import Theorems.Thm_ULHC_side1_facts
import Theorems.Thm_ULHC_side2_down
import Theorems.Thm_ULHC_side2_facts
import Theorems.Thm_ULHC_side_mem_nb
import Theorems.Thm_ULHC_side_mem_self
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_touch_cases
import Theorems.Thm_ULHC_wt_cons
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0)
  (ha2 : 2 ≤ a.n) (hT' : NoTypeIII V (applyS G a))
  {W : ℕ} (hmin : ∀ σ L', CRPathCA V G σ L' → W ≤ wt σ L')
include hs x0 hconn hG hT ha hae ha2 hT' hmin
namespace ULHC
theorem _root_.solution {σ τ : StripSpec} {L2 : List StripSpec} (hl : CR2 V G σ τ)
    (hok : ChainOK σ τ) (hch' : ¬ NoChain σ τ) (hσ : EndOK V G σ) (hσe : σ.n % 2 = 0)
    (hch : CRChain V G τ L2) (hnct : CATail (τ :: L2)) (hfar2 : ∀ w ∈ L2, ¬ Touches a w)
    {W2 : ℕ} (hvia : ViaFree V G a W2) (hW1 : wt τ L2 < W) (hW2 : a.n + wt τ L2 < W2) :
    ¬ Touches a τ := by
  rintro ⟨i, hi, j, hj, x, hx1, hx2⟩
  have nopath : ∀ σ' L', CRPathCA V G σ' L' → wt σ' L' < W → False :=
    fun σ' L' h hlt => by have := hmin σ' L' h; omega
  have hzs := chain_sig hl hok
  have core : ∀ {i j : ℕ} {x : Edge}, τ.c ≠ endCell a → 1 ≤ i → i < τ.n → j < a.n →
      x ∈ cellE (cellJ τ.c τ.s i) → x ∈ cellE (cellJ a.c a.s j) → False :=
    fun hne hii hi hj hx1 hx2 => touch_core hG hT ha hae ha2 hT' hmin hl hzs le_rfl
      (fun h => absurd h (by omega)) (fun _ => hne) hσ hσe hch hnct hfar2 hvia hW1 hW2 hii hi hj hx1 hx2
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hσe
  obtain ⟨jy, hjy, y, hy, hyu⟩ : ∃ jy < τ.n, ∃ y ∈ cellE (cellJ τ.c τ.s jy),
      y ∈ cellE (endCell σ) := by
    by_contra hn; push Not at hn; exact hch' hn
  obtain ⟨rfl, -⟩ := hok jy hjy y hy hyu
  rw [cellJ_zero] at hy
  obtain ⟨hyG, hylat, hbG, hfr, hyl⟩ := chain_start hl hok ⟨lu1, lu2⟩ hy hyu
  have hdu : τ.c ≠ endCell σ := by
    have := hl.2.2.2.2.2.2.1 0 hl.2.2.1; rwa [cellJ_zero] at this
  have hτ1 : 1 ≤ τ.n := hl.2.2.1
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  have hk2 : k % 2 = 0 := by omega
  have hpa : StripPat G a.c a.s (k + 2) := by rw [← hk]; exact ha.2.1
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => ha.2.2.1 j (by omega)
  have hsep := ha.2.2.2
  have hT'' : NoTypeIII V (flipCol G a.c a.s (k + 2)) := by unfold applyS at hT'; rwa [hk] at hT'
  have hendA : endCell a = cellJ a.c a.s (k + 1) := by unfold endCell; rw [hk]; rfl
  have haeq : (⟨a.c, a.s, k + 2⟩ : StripSpec) = a := by rw [← hk]
  -- A link from `a` straight to `τ`, when `τ` is a chain strip of `a`'s end cell.
  --
  have via_end : endCell σ = endCell a → CR2 V G a τ →
      (L2 ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell τ), y ∉ cellE (cellJ a.c a.s j)) → False := by
    intro hue hlink hfe
    have hokA : ChainOK a τ := by
      intro jj hjj z hz hze
      obtain ⟨hj0, hzl⟩ := hok jj hjj z hz (hue ▸ hze)
      refine ⟨hj0, ?_⟩
      have hzG : z ∈ G := by rcases hzl with rfl | rfl; exacts [lu1, lu2]
      obtain ⟨ea1, ea2, eab, eaf⟩ := strip_sig hpa (show k + 1 < k + 2 by omega)
      have eb : back (endCell a) a.s ∉ G := fun h => by rw [hendA] at h; have := eab.1 h; omega
      have ef : front (endCell a) a.s ∉ G := fun h => by
        rw [hendA] at h; have := (eaf.1 h).1 (by omega); omega
      rw [cellE_frame _ a.s] at hze
      simp only [Finset.mem_insert, Finset.mem_singleton] at hze
      rcases hze with rfl | rfl | rfl | rfl
      · exact absurd hzG eb
      · exact absurd hzG ef
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact hvia τ L2 ⟨⟨ha, hae, hlink, hch⟩, hokA, hnct⟩ hfar2 hfe (by rw [wt_cons]; omega)
  have hce : τ.c ≠ endCell a := fun h =>
    start_not_body hk2 hpa hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu (le_refl (k + 1)) (h.trans hendA)
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  swap
  · exact core hce hi1 hi hj hx1 hx2
  rw [cellJ_zero] at hx1
  rw [hk] at hj
  rcases touch_cases a.s hx1 hx2 with h | h | h | h | h
  · exact start_not_body hk2 hpa hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu (by omega) h
  · by_cases hjk : j ≤ k
    · exact start_not_body hk2 hpa hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu (show j + 1 ≤ k + 1 by omega) (h.trans (nb_cellJ a.c a.s j))
    obtain rfl : j = k + 1 := by omega
    rcases start_beyond hG hT hk2 hcell hpa hsep hbG hyG hylat hyl hyu hdu hs x0 hconn hT'' hfr h with
      ⟨ht, hfn⟩ | ⟨hm1, hud, hd1, hd2, hdf⟩
    · -- `τ` runs into the end cell.
      --
      have hn2 : 2 ≤ τ.n := by
        by_contra hn; exact hfn (hfr.2 (by omega))
      have h1 : cellJ τ.c τ.s 1 = endCell a := by
        rw [← nb_cellJ, cellJ_zero, ht, h, nb_nb_opp, hendA]
      have hm : back (endCell a) a.s ∈ cellE (endCell a) := by rw [cellE_frame _ a.s]; simp
      exact core hce le_rfl hn2 (show k + 1 < a.n by omega) (by rw [h1]; exact hm)
        (by rw [← hendA]; exact hm)
    · -- `τ` is a single cell with three dark sides: a shortcut to `u`.
      --
      have hd' : τ.c = cellJ a.c a.s (k + 2) := h.trans (nb_cellJ a.c a.s (k + 1))
      have hu' : endCell σ = cellJ a.c a.s (k + 3) := hud.trans (by rw [hd', nb_cellJ])
      have hcd : IsCell V (cellJ a.c a.s (k + 2)) := by
        rw [← hd']; have := hl.2.2.2.2.1 0 hτ1; rwa [cellJ_zero] at this
      rw [hd'] at hd1 hd2 hdf
      rw [hu'] at hu lu1 lu2 bu fu
      have hlink := single3_link hG hT hk2 hcell hpa hd1 hd2 hdf hu lu1 lu2 bu fu hcd
      rw [haeq] at hlink
      have hL2 : L2 = [] := by
        cases L2 with
        | nil => rfl
        | cons w L3 => have := hch.1; omega
      subst hL2
      have hokA : ChainOK a ⟨cellJ a.c a.s (k + 3), a.s, 1⟩ := by
        intro jj hjj z hz hze
        exfalso
        obtain rfl : jj = 0 := by simp only at hjj; omega
        rw [cellJ_zero] at hz
        rw [hendA] at hze
        exact along_not_mem a.c a.s (show k + 1 + 2 ≤ k + 3 by omega) hz hze
      refine hvia _ [] ⟨⟨ha, hae, hlink, rfl⟩, hokA, trivial⟩ (by simp) (fun h => absurd rfl h) ?_
      simp only [wt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hW2 ⊢
      omega
  · rcases j with _ | j
    · rw [cellJ_zero] at h
      exact start_not_behind hG hT hk2 hcell hpa hsep hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu h
    · exact start_not_body hk2 hpa hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu (show j ≤ k + 1 by omega) (by rw [h, ← nb_cellJ, nb_nb_opp])
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, hje, hyf⟩ := start_beside1 hG hT hk2 hcell hpa hsep hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu hjk h
      have hfn : front τ.c τ.s ∉ G := by
        rw [ht, (frame_opp _ a.s).2.2.2, h]
        intro hb'
        have := (side1_facts hG hT hk2 hcell hpa hsep hjk).2.1.1 hb'; omega
      have hn2 : 2 ≤ τ.n := by
        by_contra hn; exact hfn (hfr.2 (by omega))
      rcases j with _ | j
      · rw [cellJ_zero] at h
        exact start_L0 hG hT hk2 hcell hpa hsep (by rw [← h, ← ht]; exact hzs) hn2
          (by rw [← h, ← ht]; exact hl.2.2.2.2.1 1 hn2) (by rw [← h, ← hyf]; exact hyG)
      · have h1 : cellJ τ.c τ.s 1 = nb (cellJ a.c a.s j) (latA a.s) := by
          rw [← nb_cellJ, cellJ_zero, ht, h, side1_down]
        exact core hce le_rfl hn2 (show j < a.n by omega) (by rw [h1]; exact side_mem_nb _ _)
          (side_mem_self _ _)
    · obtain rfl : j = k + 1 := by omega
      obtain ⟨hue, ht⟩ := start_beside_end1 hG hT hk2 hcell hpa hsep hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu h
      have hfe : L2 ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell τ), y ∉ cellE (cellJ a.c a.s j) := by
        intro hL2 j hj y hy
        have hev : τ.n % 2 = 0 := by
          cases L2 with
          | nil => exact absurd rfl hL2
          | cons _ _ => exact hch.1
        have hτs : τ.s = a.s := ht.resolve_right (fun h' => by have := hfr.1 h'.2; omega)
        unfold endCell at hy
        rw [hτs, h] at hy
        exact beside_end_farA a.c a.s k (show 2 ≤ τ.n by omega) hy j (by omega)
      exact via_end (hue.trans hendA.symm) (haeq ▸ direct_link1 hk2 hl hue h
        (ht.imp_right fun h' => ⟨h'.1, hfr.1 h'.2⟩)) hfe
  · by_cases hjk : j ≤ k
    · obtain ⟨ht, hje, hyf⟩ := start_beside2 hG hT hk2 hcell hpa hsep hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu hjk h
      have hfn : front τ.c τ.s ∉ G := by
        rw [ht, (frame_opp _ a.s).2.2.2, h]
        intro hb'
        have := (side2_facts hG hT hk2 hcell hpa hsep hjk).2.1.1 hb'; omega
      have hn2 : 2 ≤ τ.n := by
        by_contra hn; exact hfn (hfr.2 (by omega))
      rcases j with _ | j
      · rw [cellJ_zero] at h
        exact start_R0 hG hT hk2 hcell hpa hsep (by rw [← h, ← ht]; exact hzs) hn2
          (by rw [← h, ← ht]; exact hl.2.2.2.2.1 1 hn2) (by rw [← h, ← hyf]; exact hyG)
      · have h1 : cellJ τ.c τ.s 1 = nb (cellJ a.c a.s j) (latB a.s) := by
          rw [← nb_cellJ, cellJ_zero, ht, h, side2_down]
        exact core hce le_rfl hn2 (show j < a.n by omega) (by rw [h1]; exact side_mem_nb _ _)
          (side_mem_self _ _)
    · obtain rfl : j = k + 1 := by omega
      obtain ⟨hue, ht⟩ := start_beside_end2 hG hT hk2 hcell hpa hsep hbG hyG hylat hyl lu1 lu2 bu fu hyu hdu h
      have hfe : L2 ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell τ), y ∉ cellE (cellJ a.c a.s j) := by
        intro hL2 j hj y hy
        have hev : τ.n % 2 = 0 := by
          cases L2 with
          | nil => exact absurd rfl hL2
          | cons _ _ => exact hch.1
        have hτs : τ.s = a.s := ht.resolve_right (fun h' => by have := hfr.1 h'.2; omega)
        unfold endCell at hy
        rw [hτs, h] at hy
        exact beside_end_farB a.c a.s k (show 2 ≤ τ.n by omega) hy j (by omega)
      exact via_end (hue.trans hendA.symm) (haeq ▸ direct_link2 hk2 hl hue h
        (ht.imp_right fun h' => ⟨h'.1, hfr.1 h'.2⟩)) hfe
end ULHC
