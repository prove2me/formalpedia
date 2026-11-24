-- Prove2me | solution 1 for ULHC.src_touch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:41:36.599928+00:00
-- url     : https://prove2.me/submissions/52240d61-119f-450d-9e1c-56db4545f7be

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_valid_two
import Theorems.Thm_ULHC_via_head
import Theorems.Thm_ULHC_src_notouch
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
import Theorems.Thm_ULHC_conn_lat1_opp
import Theorems.Thm_ULHC_corners4
import Theorems.Thm_ULHC_e1_chain
import Theorems.Thm_ULHC_ends_back
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_frame_opp
import Theorems.Thm_ULHC_front_join
import Theorems.Thm_ULHC_latA_ne_opp
import Theorems.Thm_ULHC_latA_opp_eq
import Theorems.Thm_ULHC_latB_ne_opp
import Theorems.Thm_ULHC_latB_opp_eq
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_nb_nb_opp
import Theorems.Thm_ULHC_outer1_body
import Theorems.Thm_ULHC_outer2_body
import Theorems.Thm_ULHC_pat_flip_off
import Theorems.Thm_ULHC_side2_back1
import Theorems.Thm_ULHC_side2_front1
import Theorems.Thm_ULHC_sig_of_pat
import Theorems.Thm_ULHC_stacked_split
import Theorems.Thm_ULHC_start_corner_edges
import Theorems.Thm_ULHC_start_side_sep
import Theorems.Thm_ULHC_strip_sig
import Theorems.Thm_ULHC_suf_cr2
import Theorems.Thm_ULHC_suf_end
import Theorems.Thm_ULHC_suf_valid
import Theorems.Thm_ULHC_touch_beyond
import Theorems.Thm_ULHC_touch_end
import Theorems.Thm_ULHC_touch_outcome
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
namespace ULHC
theorem _root_.solution {q : StripSpec} {L : List StripSpec} (hP : CRPathCA V G q L)
    (hWq : W = wt q L) (hno : ¬ ∃ σ L', CRPathCA V (applyS G a) σ L') (htq : Touches a q) :
    q.s = a.s.opp ∧ (q.c = nb a.c (latA a.s) ∨ q.c = nb a.c (latB a.s)) := by
  obtain ⟨i, hi, j, hj, x, hx1, hx2⟩ := htq
  have hntL := src_notouch hs x0 hconn hG hT ha hae ha2 hT' hmin hP hWq hno
  have nopath : ∀ σ' L', CRPathCA V G σ' L' → wt σ' L' < W → False :=
    fun σ' L' h hlt => by have := hmin σ' L' h; omega
  have hW1 : wt q L ≤ W := le_of_eq hWq.symm
  obtain ⟨⟨hv, hchq⟩, hcat⟩ := hP
  have hpq : StripPat G q.c q.s q.n := hv.2.1
  have hcq : ∀ j < q.n, IsCell V (cellJ q.c q.s j) := hv.2.2.1
  have hq2 := valid_two hv hT
  obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
  have hk2 : k % 2 = 0 := by omega
  have ha' := ha
  obtain ⟨_, hpa, hca, hsep⟩ := ha'
  rw [hk] at hpa hca hj
  have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hca j (by omega)
  have hT'' : NoTypeIII V (flipCol G a.c a.s (k + 2)) := by unfold applyS at hT'; rwa [hk] at hT'
  have hendA : endCell a = cellJ a.c a.s (k + 1) := by unfold endCell; rw [hk]; rfl
  set e := cellJ a.c a.s (k + 1) with he_def
  have via_a : ∀ w L3, L = w :: L3 → StripPat G w.c w.s w.n →
      ¬ Conn (flip G e) (back1 w.c w.s) (front1 w.c w.s) → False := by
    intro w L3 hL hpw hsplit
    subst hL
    exact hno (via_head hG hT ha hae ha2 hT' hchq hcat hntL hpw
      (by rw [hendA]; exact hsplit))
  have hqc0 : cellJ q.c q.s 0 = q.c := cellJ_zero q.c q.s
  obtain ⟨ea1, ea2, eab, eaf⟩ := strip_sig hpa (show k + 1 < k + 2 by omega)
  have el1 : lat1 e a.s ∈ G := ea1.2 (by omega)
  have el2 : lat2 e a.s ∈ G := ea2.2 (by omega)
  have eb : back e a.s ∉ G := fun h => by have := eab.1 h; omega
  have ef : front e a.s ∉ G := fun h => by have := (eaf.1 h).1 (by omega); omega
  have hce : IsCell V e := hcell (k + 1) le_rfl
  have hc0 : IsCell V a.c := by have := hcell 0 (by omega); rwa [cellJ_zero] at this
  -- **Through the end cell.**
  --
  have hR1 : ∀ i' < q.n, cellJ q.c q.s i' = e → False := by
    intro i' hi' hq
    obtain ⟨hend, hdir⟩ := touch_end hk2 hpa (sig_of_pat hpq) (Nat.zero_le _) hi' hq
    have hendq : endCell q = e := by
      unfold endCell; rw [← hq, show q.n - 1 = i' by omega]
    rcases hdir with ⟨_, hodd⟩ | ⟨hperp, hev⟩
    · cases L with
      | nil => have : q.n % 2 = 1 := hchq; omega
      | cons w L3 =>
        have hlw := hchq.2.1
        have hnt := hntL w (List.mem_cons_self ..)
        have hpw : StripPat G w.c w.s w.n := by
          have h := hlw.2.2.2.1
          rw [hendq] at h
          exact (pat_flip_off hlw.2.2.1 (fun jw hjw y hy hy' =>
            hnt ⟨jw, hjw, k + 1, by omega, y, hy, hy'⟩)).1 h
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendq] at hsplit
        exact via_a w L3 rfl hpw hsplit
    · by_cases hi0 : i' = 0
      · omega
      · have hp := cell_prev (z := q.c) (tf := q.s) (i := i') (by omega)
        rw [hq] at hp
        rcases hperp with ht | ht
        · rw [show q.s.opp = latB a.s by rw [ht, latA_opp_eq]] at hp
          rcases touch_side2_end hG hk2 hcell hpa (sig_of_pat hpq) (i := i' - 1) (Nat.zero_le _) (by omega) hp with
            ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latA_ne_opp a.s (ht.symm.trans ht')
          · exact beside_end2 hG hT hk2 hcell hpa hsep
              ((outer2_body hG hcell hpa le_rfl).2 hk2) hf hl hT''
        · rw [show q.s.opp = latA a.s by rw [ht, latB_opp_eq]] at hp
          rcases touch_side1_end hG hk2 hcell hpa (sig_of_pat hpq) (i := i' - 1) (Nat.zero_le _) (by omega) hp with
            ⟨ht', _⟩ | ⟨_, hf, hl⟩
          · exact latB_ne_opp a.s (ht.symm.trans ht')
          · exact beside_end1 hG hT hk2 hcell hpa hsep
              ((outer1_body hG hcell hpa le_rfl).2 hk2) hf hl hT''
  -- **Through the cell beyond the end cell.**
  --
  have hR2 : ∀ i' < q.n, cellJ q.c q.s i' = nb e a.s → False := by
    intro i' hi' hq
    rcases touch_beyond hG hk2 hcell hpa (sig_of_pat hpq) (Nat.zero_le _) hi' (fun _ _ => Nat.zero_le _) (fun _ => Nat.zero_le _) hq with ⟨ht, hodd, hend⟩ | ⟨ht, _, hi1⟩ |
      ⟨hperp, h0⟩
    · have hendq : endCell q = nb e a.s := by
        unfold endCell; rw [← hq, show q.n - 1 = i' by omega]
      cases L with
      | nil => have : q.n % 2 = 1 := hchq; omega
      | cons w L3 =>
        have hlw := hchq.2.1
        have hnt := hntL w (List.mem_cons_self ..)
        have hsplit := hlw.2.2.2.2.2.2.2.2.2.2.2
        rw [hendq] at hsplit
        obtain ⟨g1, g2, gb, _⟩ := strip_sig hpq hi'
        rw [hq, ht] at g1 g2 gb
        rw [(frame_opp (nb e a.s) a.s).1] at g1
        rw [(frame_opp (nb e a.s) a.s).2.1] at g2
        rw [(frame_opp (nb e a.s) a.s).2.2.1] at gb
        have ul1 := g1.2 hodd
        have ul2 := g2.2 hodd
        have hncw : NoChain q w := by
          intro jw hjw y hy hyu
          obtain ⟨rfl, hyl⟩ := hcat.1 jw hjw y hy hyu
          rw [hendq] at hyu hyl
          obtain ⟨i1, hi1, j1, hj1, x1, h1, h2⟩ := e1_chain hG hk2 hcell hpa hlw (hcat.1) hendq ht ul1 ul2 hy hyu hyl
          exact hnt ⟨i1, hi1, j1, by rw [hk]; exact hj1, x1, h1, h2⟩
        have hpw : StripPat G w.c w.s w.n := (pat_flip_off hlw.2.2.1 hncw).1 hlw.2.2.2.1
        have uf : front (nb e a.s) a.s ∉ G := fun h => by have := gb.1 h; omega
        have hcu' : IsCell V (nb e a.s) := by rw [← hq]; exact hcq i' hi'
        have hcorner : ∀ y ∈ G, ∀ jw < w.n, y ∈ cellE (cellJ w.c w.s jw) → ∀ r,
            (y.p = r ∨ y.q = r) → r ≠ front1 e a.s ∧ r ≠ front2 e a.s := by
          intro y hy jw hjw hyw r hr
          have touchy : y ∈ cellE e → False := fun h => hnt ⟨jw, hjw, k + 1, by omega, y, hyw, h⟩
          have chainy : y ∈ cellE (nb e a.s) → False := fun h =>
            hncw jw hjw y hyw (by rw [hendq]; exact h)
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
    · exact hR1 (i' + 1) hi1 (by rw [← nb_cellJ, hq, ht, nb_nb_opp])
    · subst h0
      rw [hqc0] at hq
      by_cases hm : 2 ≤ q.n
      · exact beyond_cross hG hT hk2 hcell hpa hsep hT'' hpq hperp hq hm
      · omega
  -- **Beside the start cell**: the suffix from there is a lighter path.
  --
  have hR3 : q.s = a.s.opp → ∀ i0 < q.n, i0 % 2 = 0 → i0 ≠ 0 →
      (cellJ q.c q.s i0 = nb a.c (latA a.s) ∨ cellJ q.c q.s i0 = nb a.c (latB a.s)) → False := by
    intro ht i0 hi0 hev hi00 hq
    have hsep' : ¬ Conn G (back1 (cellJ q.c q.s i0) q.s) (front1 (cellJ q.c q.s i0) q.s) := by
      obtain ⟨g1, _, _, _⟩ := strip_sig hpq hi0
      rcases hq with hq | hq <;> rw [hq] at g1 ⊢ <;> rw [ht] at g1 ⊢ <;> apply conn_lat1_opp
      · have hfar : lat1 (nb a.c (latA a.s)) a.s ∉ G := by
          rw [(frame_opp _ a.s).1] at g1; exact fun h => by have := g1.1 h; omega
        exact start_side_sep hG hT hpa (by omega) hc0 hsep hfar
      · rw [side2_back1, side2_front1]
        exact fun h => hsep ((((ends_back a.c a.s).conn hpa.1).trans h).trans
          (front_join hG hT hpa (by omega) hc0).symm)
    have hval := suf_valid hpq hcq hev hi0 hsep'
    cases L with
    | nil =>
      have hodd : q.n % 2 = 1 := hchq
      refine nopath (suf q i0) [] ⟨⟨hval, ?_⟩, trivial⟩ ?_
      · show (q.n - i0) % 2 = 1; omega
      · simp [wt, suf] at hW1 ⊢; omega
    | cons w L3 =>
      obtain ⟨hqe, hlw, hrest⟩ := hchq
      have hcr := suf_cr2 hlw hev (by omega)
      have hok' : ChainOK (suf q i0) w := by
        have := hcat.1
        unfold ChainOK at this ⊢
        rw [suf_end (by omega)]; exact this
      refine nopath (suf q i0) (w :: L3) ⟨⟨hval, ⟨by show (q.n - i0) % 2 = 0; omega, hcr, hrest⟩⟩,
        ⟨hok', hcat.2⟩⟩ ?_
      rw [wt_cons]; rw [wt_cons] at hW1; simp only [suf]; omega
  rcases touch_outcome hG hT hk2 hcell hpa hsep hT'' hpq hi hj hx1 hx2 with
    ⟨i', hi', hq⟩ | ⟨i', hi', hq⟩ | ⟨ht, i0, hi0, hev, hq⟩
  · exact (hR1 i' hi' hq).elim
  · exact (hR2 i' hi' hq).elim
  · by_cases h0 : i0 = 0
    · subst h0; rw [hqc0] at hq; exact ⟨ht, hq⟩
    · exact (hR3 ht i0 hi0 hev h0 hq).elim
end ULHC
