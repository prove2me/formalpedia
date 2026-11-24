-- Prove2me | solution 1 for ULHC.comp_clean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:45:13.228527+00:00
-- url     : https://prove2.me/submissions/8fabe1df-a6f8-461a-81ee-271c886e4003

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_valid_two
import Theorems.Thm_ULHC_endOK_of_valid
import Theorems.Thm_ULHC_via_path
import Theorems.Thm_ULHC_src_notouch
import Theorems.Thm_ULHC_src_touch
import Theorems.Thm_ULHC_besideE_offA
import Theorems.Thm_ULHC_besideE_offB
import Theorems.Thm_ULHC_besideE_cell0A
import Theorems.Thm_ULHC_besideE_cell0B
import Theorems.Thm_ULHC_mem_frame
import Theorems.Thm_ULHC_link_of_F
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_besideA_ne
import Theorems.Thm_ULHC_besideA_not_mem
import Theorems.Thm_ULHC_besideA_not_mid
import Theorems.Thm_ULHC_besideB_ne
import Theorems.Thm_ULHC_besideB_not_mem
import Theorems.Thm_ULHC_besideB_not_mid
import Theorems.Thm_ULHC_beside_end_farA
import Theorems.Thm_ULHC_beside_end_farB
import Theorems.Thm_ULHC_cellJ_add
import Theorems.Thm_ULHC_cellJ_nb_comm
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_chainOK_of_noChain
import Theorems.Thm_ULHC_chain_conn
import Theorems.Thm_ULHC_chain_transfer_CA
import Theorems.Thm_ULHC_deg2_flipCol
import Theorems.Thm_ULHC_endCell_mk
import Theorems.Thm_ULHC_farchain_CA
import Theorems.Thm_ULHC_frame_ne
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_latA_opp
import Theorems.Thm_ULHC_latB_opp
import Theorems.Thm_ULHC_mem_flipCol_out
import Theorems.Thm_ULHC_mid_touch
import Theorems.Thm_ULHC_opp_opp
import Theorems.Thm_ULHC_rev_cellJ
import Theorems.Thm_ULHC_rev_flip
import Theorems.Thm_ULHC_rev_valid
import Theorems.Thm_ULHC_shared_unique
import Theorems.Thm_ULHC_side2_lat1
import Theorems.Thm_ULHC_side_lat2
import Theorems.Thm_ULHC_sig_of_pat
import Theorems.Thm_ULHC_start_corner_edges
import Theorems.Thm_ULHC_stripPat_congr
import Theorems.Thm_ULHC_strip_sig
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {d : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j)) (hpat : StripPat G c d (k + 2))
  (hsep : ¬ Conn G (back1 c d) (front1 c d)) (hT' : NoTypeIII V (flipCol G c d (k + 2)))
include hs x0 hconn hG hT hk hcell hpat hsep hT'
namespace ULHC
theorem _root_.solution {q : StripSpec} {L : List StripSpec}
    (hP : CRPathCA V (flipCol G c d (k + 2)) q L)
    (hmin : ∀ σ L', CRPathCA V (flipCol G c d (k + 2)) σ L' → wt q L ≤ wt σ L') :
    ∃ σ L', CRPathCA V G σ L' := by
  by_contra hno'
  set F := flipCol G c d (k + 2) with hFdef
  set a : StripSpec := ⟨cellJ c d (k + 1), d.opp, k + 2⟩ with hadef
  have hcellS : ∀ j < k + 2, IsCell V (cellJ c d j) := fun j hj => hcell j (by omega)
  have hF : Deg2 V F := deg2_flipCol (k + 2) G hG hpat hcellS
  have haF : ValidStrip V F a := rev_valid hG hT hk hcell hpat hsep 
  have hFa : applyS F a = G := rev_flip G c d k
  have hTa : NoTypeIII V (applyS F a) := by rw [hFa]; exact hT
  have hae : a.n % 2 = 0 := by show (k + 2) % 2 = 0; omega
  have ha2 : 2 ≤ a.n := by show 2 ≤ k + 2; omega
  have hno : ¬ ∃ σ L', CRPathCA V (applyS F a) σ L' := by rw [hFa]; exact hno'
  have hacell : ∀ j < k + 2, cellJ a.c a.s j = cellJ c d (k + 1 - j) := fun j hj =>
    rev_cellJ c d (show j ≤ k + 1 by omega)
  have hntL := src_notouch hs x0 hconn hF hT' haF hae ha2 hTa hmin hP rfl hno
  -- The tail of `Q` is a chain of `G` once `q`'s end keeps off `s`.
  --
  have hfarQ : (L ≠ [] → ∀ y ∈ cellE (endCell q), ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i)) →
      CRChain V G q L := by
    intro hfe
    have hfar : FarChainCA F a q L := by
      cases L with
      | nil => trivial
      | cons τ L' =>
        exact farchain_CA hF haF hae ha2 (W2 := a.n + wt q (τ :: L'))
          (fun w R hP' hnt hfe' _ =>
            hno (via_path hF hT' haF hae ha2 hTa _ w R hP' rfl hnt hfe'))
          (τ :: L') q hP.1.2 hP.2 (endOK_of_valid hP.1.1)
          (fun j hj y hy hy' => hfe (by simp) y hy (k + 1 - j) (by omega)
            (by rw [← hacell j hj]; exact hy'))
          hntL le_rfl
    have := chain_transfer_CA hF hT' haF hae ha2 hTa L q (endOK_of_valid hP.1.1) hP.1.2 hP.2 hfar
    rwa [hFa] at this
  have hv := hP.1.1
  have hq1 : 1 ≤ q.n := hv.1
  have hq2 := valid_two hv hT'
  have hpqF : StripPat F q.c q.s q.n := hv.2.1
  have hcq := hv.2.2.1
  have hsepF := hv.2.2.2
  have hvs : ValidStrip V G ⟨c, d, k + 2⟩ := ⟨by show 1 ≤ k + 2; omega, hpat, hcellS, hsep⟩
  by_cases htq : Touches a q
  · obtain ⟨hqs, hqc⟩ := src_touch hs x0 hconn hF hT' haF hae ha2 hTa hmin hP rfl hno htq
    simp only [hadef, opp_opp, latA_opp, latB_opp] at hqs hqc
    rcases hqc with hqc | hqc
    · -- `q` starts beside the end cell across `latA`.
      --
      have hzq : ∀ j, cellJ q.c q.s j = cellJ (nb (cellJ c d (k + 1)) (latA d)) d j :=
        fun j => by rw [hqs, hqc]
      have hoff1 : ∀ j, 1 ≤ j → ∀ y ∈ cellE (cellJ q.c q.s j), ∀ i ≤ k + 1,
          y ∉ cellE (cellJ c d i) := fun j hj1 y hy => besideE_offA c d k hj1 (by rw [← hzq]; exact hy)
      have hx0 : lat2 q.c q.s = lat1 (cellJ c d (k + 1)) d := by rw [hqs, hqc, side_lat2]
      have hoff0 : ∀ y ∈ cellE q.c, y ≠ lat2 q.c q.s → ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) :=
        fun y hy hne => besideE_cell0A c d k (by rw [← hqc]; exact hy) (by rw [← hx0]; exact hne)
      obtain ⟨ea1, ea2, _, _⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
      have elx : lat1 (cellJ c d (k + 1)) d ∈ G := ea1.2 (by omega)
      have fne := frame_ne q.c q.s
      have hsigF := sig_of_pat hpqF
      have hsigG : SigFrom G q.c q.s q.n 1 := by
        intro i hi1 hin
        have hs' : ∀ y ∈ cellE (cellJ q.c q.s i), (y ∈ F ↔ y ∈ G) := fun y hy =>
          mem_flipCol_out (fun i' hi' => hoff1 i hi1 y hy i' (by omega))
        obtain ⟨g1, g2, gb, gf⟩ := hsigF i (Nat.zero_le _) hin
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [← hs' _ (mem_frame _ q.s (Or.inl rfl))]; exact g1
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inl rfl)))]; exact g2
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inl rfl))))]; exact gb
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inr rfl))))]; exact gf
      have hbG : back q.c q.s ∈ G := by
        have hb := hpqF.1
        rwa [mem_flipCol_out (fun i hi => hoff0 _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inl rfl))))
          fne.2.1 i (by omega))] at hb
      have hfG : front q.c q.s ∉ G := by
        have hf0 := (hsigF 0 (Nat.zero_le _) (by omega)).2.2.2
        rw [cellJ_zero] at hf0
        intro h
        rw [← mem_flipCol_out (F := G) (c := c) (s := d) (n := k + 2) (fun i hi => hoff0 _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inr rfl))))
          fne.2.2.2.1 i (by omega))] at h
        have := (hf0.1 h).2 (by omega); omega
      have hcg : Conn G (back1 q.c q.s) (front1 q.c q.s) :=
        chain_conn hG hT hq1 hsigG (fun _ => hcq 1 (by omega)) hbG
          ⟨fun h => absurd h hfG, fun h => by omega⟩ (Or.inr (by rw [hx0]; exact elx))
      have hlink := link_of_F hG hT hk hcell hpat hsep hq1 hpqF hcq
        (fun j hj i hi y hy => by
          have hi' : i + 1 < k + 2 := hi
          rw [hzq, cellJ_nb_comm, cellJ_add] at hy
          exact besideA_not_mem c d (j := 0) (show i < k + 1 + j by omega)
            (by rw [cellJ_zero]; exact hy))
        (fun j _ => by rw [hzq]; exact besideA_ne c d (k + 1) j (k + 1))
        (fun _ y hy => beside_end_farA c d k (show 2 ≤ q.n by omega)
          (by unfold endCell at hy; rw [hzq] at hy; exact hy) (k + 1) (by omega))
        (by rw [hqs, hqc]; exact (besideA_not_mid c d k (Or.inl rfl)).1)
        (by rw [hqs, hqc]; exact (besideA_not_mid c d k (Or.inl rfl)).2) hcg hsepF
      have hok : ChainOK ⟨c, d, k + 2⟩ q := by
        intro j hj y hy hye
        rw [endCell_mk] at hye ⊢
        rcases Nat.eq_zero_or_pos j with rfl | hj1
        · rw [cellJ_zero] at hy
          exact ⟨rfl, Or.inl (by rw [shared_unique hqc hye hy, lat1_eq])⟩
        · exact absurd hye (hoff1 j hj1 y hy (k + 1) le_rfl)
      have hchG := hfarQ (fun _ y hy i hi =>
        hoff1 (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) i hi)
      exact hno' ⟨_, q :: L, ⟨⟨hvs, by show (k + 2) % 2 = 0; omega, hlink, hchG⟩, hok, hP.2⟩⟩
    · -- `q` starts beside the end cell across `latB`.
      --
      have hzq : ∀ j, cellJ q.c q.s j = cellJ (nb (cellJ c d (k + 1)) (latB d)) d j :=
        fun j => by rw [hqs, hqc]
      have hoff1 : ∀ j, 1 ≤ j → ∀ y ∈ cellE (cellJ q.c q.s j), ∀ i ≤ k + 1,
          y ∉ cellE (cellJ c d i) := fun j hj1 y hy => besideE_offB c d k hj1 (by rw [← hzq]; exact hy)
      have hx0 : lat1 q.c q.s = lat2 (cellJ c d (k + 1)) d := by rw [hqs, hqc, side2_lat1]
      have hoff0 : ∀ y ∈ cellE q.c, y ≠ lat1 q.c q.s → ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) :=
        fun y hy hne => besideE_cell0B c d k (by rw [← hqc]; exact hy) (by rw [← hx0]; exact hne)
      obtain ⟨ea1, ea2, _, _⟩ := strip_sig hpat (show k + 1 < k + 2 by omega)
      have elx : lat2 (cellJ c d (k + 1)) d ∈ G := ea2.2 (by omega)
      have fne := frame_ne q.c q.s
      have hsigF := sig_of_pat hpqF
      have hsigG : SigFrom G q.c q.s q.n 1 := by
        intro i hi1 hin
        have hs' : ∀ y ∈ cellE (cellJ q.c q.s i), (y ∈ F ↔ y ∈ G) := fun y hy =>
          mem_flipCol_out (fun i' hi' => hoff1 i hi1 y hy i' (by omega))
        obtain ⟨g1, g2, gb, gf⟩ := hsigF i (Nat.zero_le _) hin
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [← hs' _ (mem_frame _ q.s (Or.inl rfl))]; exact g1
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inl rfl)))]; exact g2
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inl rfl))))]; exact gb
        · rw [← hs' _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inr rfl))))]; exact gf
      have hbG : back q.c q.s ∈ G := by
        have hb := hpqF.1
        rwa [mem_flipCol_out (fun i hi => hoff0 _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inl rfl))))
          fne.1 i (by omega))] at hb
      have hfG : front q.c q.s ∉ G := by
        have hf0 := (hsigF 0 (Nat.zero_le _) (by omega)).2.2.2
        rw [cellJ_zero] at hf0
        intro h
        rw [← mem_flipCol_out (F := G) (c := c) (s := d) (n := k + 2) (fun i hi => hoff0 _ (mem_frame _ q.s (Or.inr (Or.inr (Or.inr rfl))))
          fne.2.2.1 i (by omega))] at h
        have := (hf0.1 h).2 (by omega); omega
      have hcg : Conn G (back1 q.c q.s) (front1 q.c q.s) :=
        chain_conn hG hT hq1 hsigG (fun _ => hcq 1 (by omega)) hbG
          ⟨fun h => absurd h hfG, fun h => by omega⟩ (Or.inl (by rw [hx0]; exact elx))
      have hlink := link_of_F hG hT hk hcell hpat hsep hq1 hpqF hcq
        (fun j hj i hi y hy => by
          have hi' : i + 1 < k + 2 := hi
          rw [hzq, cellJ_nb_comm, cellJ_add] at hy
          exact besideB_not_mem c d (j := 0) (show i < k + 1 + j by omega)
            (by rw [cellJ_zero]; exact hy))
        (fun j _ => by rw [hzq]; exact besideB_ne c d (k + 1) j (k + 1))
        (fun _ y hy => beside_end_farB c d k (show 2 ≤ q.n by omega)
          (by unfold endCell at hy; rw [hzq] at hy; exact hy) (k + 1) (by omega))
        (by rw [hqs, hqc]; exact (besideB_not_mid c d k (Or.inl rfl)).1)
        (by rw [hqs, hqc]; exact (besideB_not_mid c d k (Or.inl rfl)).2) hcg hsepF
      have hok : ChainOK ⟨c, d, k + 2⟩ q := by
        intro j hj y hy hye
        rw [endCell_mk] at hye ⊢
        rcases Nat.eq_zero_or_pos j with rfl | hj1
        · rw [cellJ_zero] at hy
          exact ⟨rfl, Or.inr (by rw [shared_unique hqc hye hy, lat2_eq])⟩
        · exact absurd hye (hoff1 j hj1 y hy (k + 1) le_rfl)
      have hchG := hfarQ (fun _ y hy i hi =>
        hoff1 (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) i hi)
      exact hno' ⟨_, q :: L, ⟨⟨hvs, by show (k + 2) % 2 = 0; omega, hlink, hchG⟩, hok, hP.2⟩⟩
  · -- `q` keeps off `s`.
    --
    have hoff : ∀ j < q.n, ∀ y ∈ cellE (cellJ q.c q.s j), ∀ i ≤ k + 1,
        y ∉ cellE (cellJ c d i) := by
      intro j hj y hy i hi hyi
      exact htq ⟨j, hj, k + 1 - i, by show k + 1 - i < k + 2; omega, y, hy, by
        rw [hacell _ (by omega), show k + 1 - (k + 1 - i) = i by omega]; exact hyi⟩
    have hsame : ∀ j < q.n, ∀ y ∈ cellE (cellJ q.c q.s j), (y ∈ F ↔ y ∈ G) := fun j hj y hy =>
      mem_flipCol_out (fun i hi => hoff j hj y hy i (by omega))
    have hpqG : StripPat G q.c q.s q.n := by
      obtain ⟨m, hm⟩ : ∃ m, q.n = m + 1 := ⟨q.n - 1, by omega⟩
      rw [hm] at hpqF hsame ⊢
      exact (stripPat_congr hsame).1 hpqF
    have hchG := hfarQ (fun _ y hy i hi =>
      hoff (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) i hi)
    by_cases hcg : Conn G (back1 q.c q.s) (front1 q.c q.s)
    · have hmid : ∀ p, (∃ j < q.n, ∃ x ∈ G, (x.p = p ∨ x.q = p) ∧ x ∈ cellE (cellJ q.c q.s j)) →
          ¬ IsMid c d k p := by
        rintro p ⟨j, hj, x, hx, hxp, hxw⟩ hm
        obtain ⟨i, hi, hxi⟩ := mid_touch hG hpat hcell hm hx hxp
        exact hoff j hj x hxw i (by omega) hxi
      obtain ⟨⟨hb, hbp, hb0⟩, jf, hjf, xf, hxf, hxfp, hxfw⟩ := start_corner_edges hpqG hq1
      have hlink := link_of_F hG hT hk hcell hpat hsep hq1 hpqF hcq
        (fun j hj i hi y hy => by
          have hi' : i + 1 < k + 2 := hi
          exact hoff j hj y hy i (by omega))
        (fun j hj h => hoff j hj _ (by rw [h]; exact mem_frame _ d (Or.inr (Or.inr (Or.inl rfl))))
          (k + 1) le_rfl (mem_frame _ d (Or.inr (Or.inr (Or.inl rfl)))))
        (fun _ y hy => hoff (q.n - 1) (by omega) y (by unfold endCell at hy; exact hy) (k + 1) le_rfl)
        (hmid _ ⟨0, by omega, _, hb, hbp, hb0⟩) (hmid _ ⟨jf, hjf, xf, hxf, hxfp, hxfw⟩) hcg hsepF
      have hok : ChainOK ⟨c, d, k + 2⟩ q := chainOK_of_noChain (fun j hj y hy hye =>
        hoff j hj y hy (k + 1) le_rfl (by rwa [endCell_mk] at hye))
      exact hno' ⟨_, q :: L, ⟨⟨hvs, by show (k + 2) % 2 = 0; omega, hlink, hchG⟩, hok, hP.2⟩⟩
    · exact hno' ⟨q, L, ⟨⟨⟨hq1, hpqG, hcq, hcg⟩, hchG⟩, hP.2⟩⟩
end ULHC
