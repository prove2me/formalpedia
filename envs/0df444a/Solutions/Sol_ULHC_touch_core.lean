-- Prove2me | solution 1 for ULHC.touch_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:30:27.87069+00:00
-- url     : https://prove2.me/submissions/32929f8d-999f-417a-a9e0-ca01c0a8b129

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_e1_chain
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_conn
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_Ends_ne_at
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_alt_touch
import Theorems.Thm_ULHC_back1_nb
import Theorems.Thm_ULHC_back1_ne_front1_nb
import Theorems.Thm_ULHC_back2_nb
import Theorems.Thm_ULHC_back2_ne_front2_nb
import Theorems.Thm_ULHC_beside_end1
import Theorems.Thm_ULHC_beside_end2
import Theorems.Thm_ULHC_beyond_cross
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_cell_prev
import Theorems.Thm_ULHC_chainOK_of_noChain
import Theorems.Thm_ULHC_conn_lat1_opp
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_cross_to_back
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_frame_latA
import Theorems.Thm_ULHC_frame_latB
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_front_join
import Theorems.Thm_ULHC_front_to_back
import Theorems.Thm_ULHC_latA_ne_opp
import Theorems.Thm_ULHC_latA_opp_eq
import Theorems.Thm_ULHC_latB_ne_opp
import Theorems.Thm_ULHC_latB_opp_eq
import Theorems.Thm_ULHC_link_a
import Theorems.Thm_ULHC_mem_flip_off
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_nb_nb_opp
import Theorems.Thm_ULHC_outer1_body
import Theorems.Thm_ULHC_outer2_body
import Theorems.Thm_ULHC_pat_flip_off
import Theorems.Thm_ULHC_side2_back1
import Theorems.Thm_ULHC_side2_front1
import Theorems.Thm_ULHC_side_mem_nb
import Theorems.Thm_ULHC_side_mem_self
import Theorems.Thm_ULHC_split_core
import Theorems.Thm_ULHC_stacked_split
import Theorems.Thm_ULHC_start_corner_edges
import Theorems.Thm_ULHC_start_side_sep
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_suf_cr2
import Theorems.Thm_ULHC_suf_end
import Theorems.Thm_ULHC_suf_validW
import Theorems.Thm_ULHC_touch_beyond
import Theorems.Thm_ULHC_touch_end
import Theorems.Thm_ULHC_touch_outcomeW
import Theorems.Thm_ULHC_touch_side1_end
import Theorems.Thm_ULHC_touch_side2_end
import Theorems.Thm_ULHC_two_at
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
omit hs x0 hconn
namespace ULHC
theorem _root_.solution {σ τ : StripSpec} {i0 : ℕ} {L2 : List StripSpec} (hl : CR2 V G σ τ)
    (hzs : SigFrom G τ.c τ.s τ.n i0) (hi01 : i0 ≤ 1) (hz0 : i0 = 0 → NoChain σ τ)
    (hne_e : i0 = 1 → τ.c ≠ endCell a)
    (hσ : EndOK V G σ) (hσe : σ.n % 2 = 0) (hch : CRChain V G τ L2)
    (hnct : CATail (τ :: L2)) (hfar2 : ∀ w ∈ L2, ¬ Touches a w)
    {W2 : ℕ} (hvia : ViaFree V G a W2) (hW1 : wt τ L2 < W) (hW2 : a.n + wt τ L2 < W2) {i j : ℕ} (hii : i0 ≤ i) (hi : i < τ.n) (hj : j < a.n)
    {x : Edge} (hx1 : x ∈ cellE (cellJ τ.c τ.s i)) (hx2 : x ∈ cellE (cellJ a.c a.s j)) :
    False := by
  have nopath : ∀ σ' L', CRPathCA V G σ' L' → wt σ' L' < W → False :=
    fun σ' L' h hlt => by have := hmin σ' L' h; omega
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  have hk2 : k % 2 = 0 := by omega
  obtain ⟨_, hpa, hca, hsep⟩ := ha
  rw [hk] at hpa hca hj
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hca j (by omega)
  have hT'' : NoTypeIII V (flipCol G a.c a.s (k + 2)) := by unfold applyS at hT'; rwa [hk] at hT'
  have hendA : endCell a = cellJ a.c a.s (k + 1) := by unfold endCell; rw [hk]; rfl
  set e := cellJ a.c a.s (k + 1) with he_def
  obtain ⟨h2σ, _, hτ1, hpτu, hcτ, hso, hne, hen, _, _, hcg, hcu⟩ := hl
  -- Where the whole pattern of `τ` is needed (start cell cases), `τ` has no shared side.
  --
  have hpτ0 : i0 = 0 → StripPat G τ.c τ.s τ.n := fun h => (pat_flip_off hτ1 (hz0 h)).1 hpτu
  have hzi : ∀ i', i0 ≤ i' → i' < τ.n → _ := fun i' h1 h2 => hzs i' h1 h2
  obtain ⟨hu, lu1, lu2, bu, fu⟩ := hσ hσe
  set u' := endCell σ
  -- Shortcut through `a` to the successor `w` of `τ`, once `w`'s start is split by `e`.
  --
  have via_a : ∀ w L3, L2 = w :: L3 → StripPat G w.c w.s w.n →
      ¬ Conn (flip G e) (back1 w.c w.s) (front1 w.c w.s) → False := by
    intro w L3 hL hpw hsplit
    subst hL
    obtain ⟨_, hlw, hrest⟩ := hch
    have hnt := hfar2 w (List.mem_cons_self ..)
    have hw1 : 1 ≤ w.n := hlw.2.2.1
    have hlink : CR2 V G a w := link_a hG ⟨by omega, by rw [hk]; exact hpa,
      fun j hj => hca j (by rw [hk] at hj; exact hj), hsep⟩ hae ha2 hw1 hpw hlw.2.2.2.2.1 hnt
      hlw.2.2.2.2.2.2.2.2.2.2.1 (by rw [hendA]; exact hsplit)
    refine hvia w L3 ⟨⟨⟨by omega, by rw [hk]; exact hpa,
      fun j hj => hca j (by rw [hk] at hj; exact hj), hsep⟩, hae, hlink, hrest⟩,
      ⟨chainOK_of_noChain (fun jw hjw y hy hye => hnt ⟨jw, hjw, k + 1, by omega, y, hy,
        by rw [hendA] at hye; exact hye⟩), hnct.2⟩⟩
      (fun x hx => hfar2 x (List.mem_cons_of_mem _ hx))
      (fun _ j hj y hy hy' => hnt ⟨w.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy, hy'⟩) ?_
    rw [wt_cons]; rw [wt_cons] at hW2; omega
  have hτc0 : cellJ τ.c τ.s 0 = τ.c := cellJ_zero τ.c τ.s
  obtain ⟨ea1, ea2, eab, eaf⟩ := strip_sig hpa (show k + 1 < k + 2 by omega)
  have el1 : lat1 e a.s ∈ G := ea1.2 (by omega)
  have el2 : lat2 e a.s ∈ G := ea2.2 (by omega)
  have eb : back e a.s ∉ G := fun h => by have := eab.1 h; omega
  have ef : front e a.s ∉ G := fun h => by have := (eaf.1 h).1 (by omega); omega
  have hce : IsCell V e := hcell (k + 1) le_rfl
  have hc0 : IsCell V a.c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  -- `u'` (the previous end) differs from `e` and from the cell beyond, when `τ` starts at one
  -- of them and keeps off `u'`.
  --
  have off_e : ∀ y ∈ cellE e, y ∉ cellE u' → (y ∈ flip G u' ↔ y ∈ G) := fun y _ hy =>
    mem_flip_off hy
  -- **Through the end cell.**
  --
  have hR1 : ∀ i', i0 ≤ i' → i' < τ.n → cellJ τ.c τ.s i' = e → False := by
    intro i' hi0' hi' hq
    obtain ⟨hend, hdir⟩ := touch_end hk2 hpa hzs hi0' hi' hq
    have hendτ : endCell τ = e := by
      unfold endCell; rw [← hq, show τ.n - 1 = i' by omega]
    rcases hdir with ⟨_, hodd⟩ | ⟨hperp, hev⟩
    · cases L2 with
      | nil => have : τ.n % 2 = 1 := hch; omega
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hfar2 w (List.mem_cons_self ..)
        have hpw : StripPat G w.c w.s w.n := by
          have h := hlw.2.2.2.1
          rw [hendτ] at h
          exact (pat_flip_off hlw.2.2.1 (fun jw hjw y hy hy' =>
            hnt ⟨jw, hjw, k + 1, by omega, y, hy, hy'⟩)).1 h
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendτ] at hsplit
        exact via_a w L3 rfl hpw hsplit
    · by_cases hi0 : i' = 0
      · subst hi0
        have hz00 : i0 = 0 := by omega
        have hnc := hz0 hz00
        have hpτ := hpτ0 hz00
        rw [hτc0] at hq
        have hwe : u' ≠ e := fun h => hne 0 (by omega) (by rw [hτc0, hq, h])
        have hwu : u' ≠ nb e a.s := fun h => hnc 0 (by omega) (sideEdge e a.s)
          (by rw [hτc0, hq]; exact side_mem_self e a.s)
          (by show sideEdge e a.s ∈ cellE u'; rw [h]; exact side_mem_nb e a.s)
        have hoff : ∀ y ∈ cellE e, y ∉ cellE u' := fun y hy =>
          hnc 0 (by omega) y (by rw [hτc0, hq]; exact hy)
        have m1 : lat1 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have m2 : lat2 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have hsp := hcu
        rw [hq] at hsp
        exact split_core hG hT hk2 hcell hpa hsep hT'' hu lu1 lu2 bu fu hwe hwu
          (cross_to_back hperp ((mem_flip_off (hoff _ m1)).2 el1)
            ((mem_flip_off (hoff _ m2)).2 el2) hsp)
      · have hp := cell_prev (z := τ.c) (tf := τ.s) (i := i') (by omega)
        rw [hq] at hp
        rcases hperp with ht | ht
        · rw [show τ.s.opp = latB a.s by rw [ht, latA_opp_eq]] at hp
          rcases touch_side2_end hG hk2 hcell hpa hzs (i := i' - 1) (by omega) (by omega) hp with
            ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latA_ne_opp a.s (ht.symm.trans ht')
          · exact beside_end2 hG hT hk2 hcell hpa hsep
              ((outer2_body hG hcell hpa le_rfl).2 hk2) hf hl hT''
        · rw [show τ.s.opp = latA a.s by rw [ht, latB_opp_eq]] at hp
          rcases touch_side1_end hG hk2 hcell hpa hzs (i := i' - 1) (by omega) (by omega) hp with
            ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latB_ne_opp a.s (ht.symm.trans ht')
          · exact beside_end1 hG hT hk2 hcell hpa hsep
              ((outer1_body hG hcell hpa le_rfl).2 hk2) hf hl hT''
  -- **Through the cell beyond the end cell.**
  --
  have hR2 : ∀ i', i0 ≤ i' → i' < τ.n → cellJ τ.c τ.s i' = nb e a.s → False := by
    intro i' hi0' hi' hq
    have hpvs : τ.s = a.s → 1 ≤ i' → i0 ≤ i' - 1 := by
      intro ht hi1
      by_contra hc
      have hi1' : i' = 1 := by omega
      have hz1 : i0 = 1 := by omega
      have hp := cell_prev (z := τ.c) (tf := τ.s) (i := i') (by omega)
      rw [hq, ht, nb_nb_opp, hi1', show 1 - 1 = 0 from rfl, cellJ_zero] at hp
      exact hne_e hz1 (by rw [hendA]; exact hp)
    rcases touch_beyond hG hk2 hcell hpa hzs hi0' hi' hpvs (fun _ => by omega) hq with ⟨ht, hodd, hend⟩ | ⟨ht, _, hi1⟩ |
      ⟨hperp, h0⟩
    · have hendτ : endCell τ = nb e a.s := by
        unfold endCell; rw [← hq, show τ.n - 1 = i' by omega]
      cases L2 with
      | nil => have : τ.n % 2 = 1 := hch; omega
      | cons w L3 =>
        have hlw := hch.2.1
        have hnt := hfar2 w (List.mem_cons_self ..)
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendτ] at hsplit
        obtain ⟨g1, g2, gb, _⟩ := hzs i' hi0' hi'
        rw [hq, ht] at g1 g2 gb
        rw [(frame_opp (nb e a.s) a.s).1] at g1
        rw [(frame_opp (nb e a.s) a.s).2.1] at g2
        rw [(frame_opp (nb e a.s) a.s).2.2.1] at gb
        have ul1 := g1.2 hodd
        have ul2 := g2.2 hodd
        have hncw : NoChain τ w := by
          intro jw hjw y hy hyu
          obtain ⟨rfl, hyl⟩ := hnct.1 jw hjw y hy hyu
          rw [hendτ] at hyu hyl
          obtain ⟨i1, hi1, j1, hj1, x1, h1, h2⟩ := e1_chain hG hk2 hcell hpa hlw (hnct.1) hendτ ht ul1 ul2 hy hyu hyl
          exact hnt ⟨i1, hi1, j1, by rw [hk]; exact hj1, x1, h1, h2⟩
        have hpw : StripPat G w.c w.s w.n := (pat_flip_off hlw.2.2.1 hncw).1 hlw.2.2.2.1
        have uf : front (nb e a.s) a.s ∉ G := fun h => by have := gb.1 h; omega
        have hcu' : IsCell V (nb e a.s) := by rw [← hq]; exact hcτ i' hi'
        have hcorner : ∀ y ∈ G, ∀ jw < w.n, y ∈ cellE (cellJ w.c w.s jw) → ∀ r,
            (y.p = r ∨ y.q = r) → r ≠ front1 e a.s ∧ r ≠ front2 e a.s := by
          intro y hy jw hjw hyw r hr
          have touchy : y ∈ cellE e → False := fun h => hnt ⟨jw, hjw, k + 1, by omega, y, hyw, h⟩
          have chainy : y ∈ cellE (nb e a.s) → False := fun h =>
            hncw jw hjw y hyw (by rw [hendτ]; exact h)
          constructor
          · rintro rfl
            have i2 := (ends_lat1 (nb e a.s) a.s).inc_iff (front1 e a.s) |>.2
              (Or.inl (back1_nb e a.s).symm)
            have hne2 : lat1 e a.s ≠ lat1 (nb e a.s) a.s := (ends_lat1 e a.s).ne_at
              (by have := ends_lat1 (nb e a.s) a.s; rwa [back1_nb] at this)
              (back1_ne_front1_nb e a.s)
            rcases two_at (hG.2 _ (corners4 hce a.s).2.2.1) el1 ul1
              ((ends_lat1 e a.s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, cellE_frame e a.s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e a.s) a.s]; simp)
          · rintro rfl
            have i2 := (ends_lat2 (nb e a.s) a.s).inc_iff (front2 e a.s) |>.2
              (Or.inl (back2_nb e a.s).symm)
            have hne2 : lat2 e a.s ≠ lat2 (nb e a.s) a.s := (ends_lat2 e a.s).ne_at
              (by have := ends_lat2 (nb e a.s) a.s; rwa [back2_nb] at this)
              (back2_ne_front2_nb e a.s)
            rcases two_at (hG.2 _ (corners4 hce a.s).2.2.2) el2 ul2
              ((ends_lat2 e a.s).inc_iff _ |>.2 (Or.inr rfl)) i2 hne2 hy hr with h | h
            · exact touchy (by rw [h, cellE_frame e a.s]; simp)
            · exact chainy (by rw [h, cellE_frame (nb e a.s) a.s]; simp)
        have hw1 : 1 ≤ w.n := hlw.2.2.1
        obtain ⟨⟨hb, hbp, hb0⟩, jf, hjf, xf, hxf, hxfp, hxfw⟩ := start_corner_edges hpw hw1
        have cb := hcorner _ hb 0 (by omega) hb0 _ hbp
        have cf := hcorner _ hxf jf hjf hxfw _ hxfp
        have hss := stacked_split hG hce hcu' el1 el2 eb ef ul1 ul2 uf cb.1 cb.2 cf.1 cf.2
        exact via_a w L3 rfl hpw (fun h => hsplit (hss.1 h))
    · exact hR1 (i' + 1) (by omega) hi1 (by rw [← nb_cellJ, hq, ht, nb_nb_opp])
    · subst h0
      have hz00 : i0 = 0 := by omega
      have hnc := hz0 hz00
      have hpτ := hpτ0 hz00
      rw [hτc0] at hq
      by_cases hm : 2 ≤ τ.n
      · exact beyond_cross hG hT hk2 hcell hpa hsep hT'' hpτ hperp hq hm
      · have hm1 : τ.n = 1 := by omega
        obtain ⟨_, _, gb, gf⟩ := strip_sig hpτ (show 0 < τ.n by omega)
        rw [hτc0, hq] at gb gf
        have hbz := gb.2 rfl
        have hfz := gf.2 ⟨fun h => by omega, fun h => by omega⟩
        have hl12 : lat1 (nb e a.s) a.s ∈ G ∧ lat2 (nb e a.s) a.s ∈ G := by
          rcases hperp with ht | ht <;> rw [ht] at hbz hfz
          · rw [(frame_latA _ _).1] at hfz; rw [(frame_latA _ _).2.1] at hbz; exact ⟨hfz, hbz⟩
          · rw [(frame_latB _ _).1] at hfz; rw [(frame_latB _ _).2.1] at hbz; exact ⟨hbz, hfz⟩
        have hoffu : ∀ y ∈ cellE (nb e a.s), y ∉ cellE u' := fun y hy =>
          hnc 0 (by omega) y (by rw [hτc0, hq]; exact hy)
        have hwu : u' ≠ nb e a.s := fun h => hne 0 (by omega) (by rw [hτc0, hq, h])
        have hwe : u' ≠ e := fun h => hoffu (sideEdge e a.s) (side_mem_nb e a.s)
          (by rw [h]; exact side_mem_self e a.s)
        have hoffe : ∀ y ∈ cellE e, y ∉ cellE u' := by
          intro y hy hy'
          rcases alt_touch hG hT hk2 hcell hpa hsep lu1 lu2 bu fu
            (show k + 1 < k + 2 by omega) hy' hy with h | h
          · exact hwe h
          · exact hwu h
        have m1 : lat1 (nb e a.s) a.s ∈ cellE (nb e a.s) := by rw [cellE_frame _ a.s]; simp
        have m2 : lat2 (nb e a.s) a.s ∈ cellE (nb e a.s) := by rw [cellE_frame _ a.s]; simp
        have m1e : lat1 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have m2e : lat2 e a.s ∈ cellE e := by rw [cellE_frame e a.s]; simp
        have hsp := hcu
        rw [hq] at hsp
        have h1 := cross_to_back hperp ((mem_flip_off (hoffu _ m1)).2 hl12.1)
          ((mem_flip_off (hoffu _ m2)).2 hl12.2) hsp
        rw [back1_nb, back2_nb] at h1
        exact split_core hG hT hk2 hcell hpa hsep hT'' hu lu1 lu2 bu fu hwe hwu
          (front_to_back ((mem_flip_off (hoffe _ m1e)).2 el1)
            ((mem_flip_off (hoffe _ m2e)).2 el2) h1)
  -- **Beside the start cell**: the suffix from there is a lighter path.
  --
  have hR3 : τ.s = a.s.opp → ∀ ie, i0 ≤ ie → ie < τ.n → ie % 2 = 0 →
      (cellJ τ.c τ.s ie = nb a.c (latA a.s) ∨ cellJ τ.c τ.s ie = nb a.c (latB a.s)) → False := by
    intro ht ie hie hi0 hev hq
    have hsep' : ¬ Conn G (back1 (cellJ τ.c τ.s ie) τ.s) (front1 (cellJ τ.c τ.s ie) τ.s) := by
      obtain ⟨g1, _, _, _⟩ := hzs ie hie hi0
      rcases hq with hq | hq <;> rw [hq] at g1 ⊢ <;> rw [ht] at g1 ⊢ <;> apply conn_lat1_opp
      · have hfar : lat1 (nb a.c (latA a.s)) a.s ∉ G := by
          rw [(frame_opp _ a.s).1] at g1; exact fun h => by have := g1.1 h; omega
        exact start_side_sep hG hT hpa (by omega) hc0 hsep hfar
      · rw [side2_back1, side2_front1]
        exact fun h => hsep ((((ends_back a.c a.s).conn hpa.1).trans h).trans
          (front_join hG hT hpa (by omega) hc0).symm)
    have hval := suf_validW hzs hcτ hie hev hi0 hsep'
    cases L2 with
    | nil =>
      have hodd : τ.n % 2 = 1 := hch
      refine nopath (suf τ ie) [] ⟨⟨hval, ?_⟩, trivial⟩ ?_
      · show (τ.n - ie) % 2 = 1; omega
      · simp [wt, suf] at hW1 ⊢; omega
    | cons w L3 =>
      obtain ⟨hτe, hlw, hrest⟩ := hch
      have hcr := suf_cr2 hlw hev (by omega)
      have hok' : ChainOK (suf τ ie) w := by
        have := hnct.1
        unfold ChainOK at this ⊢
        rw [suf_end (by omega)]; exact this
      refine nopath (suf τ ie) (w :: L3) ⟨⟨hval, ⟨by show (τ.n - ie) % 2 = 0; omega, hcr, hrest⟩⟩,
        ⟨hok', hnct.2⟩⟩ ?_
      rw [wt_cons]; rw [wt_cons] at hW1; simp only [suf]; omega
  rcases touch_outcomeW hG hT hk2 hcell hpa hsep hT'' hzs hii hi hj hx1 hx2 with
    ⟨i', hle, hi', hq⟩ | ⟨i', hle, hi', hq⟩ | ⟨ht, ie, hle, hi0, hev, hq⟩
  · exact hR1 i' (by omega) hi' hq
  · exact hR2 i' (by omega) hi' hq
  · exact hR3 ht ie (by omega) hi0 hev hq
end ULHC
