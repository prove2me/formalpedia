-- Prove2me | solution 1 for ULHC.farchain_CA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:19:48.448859+00:00
-- url     : https://prove2.me/submissions/a9cf8abc-191d-41df-a713-088aa62305fb

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_chain_corner_edges
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_Ends_inc_iff
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellE_frame
import Theorems.Thm_ULHC_cellJ_zero
import Theorems.Thm_ULHC_chainOK_of_noChain
import Theorems.Thm_ULHC_chain_sig
import Theorems.Thm_ULHC_chain_start
import Theorems.Thm_ULHC_endOK_of_link
import Theorems.Thm_ULHC_ends_lat1
import Theorems.Thm_ULHC_ends_lat2
import Theorems.Thm_ULHC_link_a
import Theorems.Thm_ULHC_mid_touch
import Theorems.Thm_ULHC_pat_flip_off
import Theorems.Thm_ULHC_start_corner_edges
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
omit hs x0 hconn hT hT' hmin
namespace ULHC
theorem _root_.solution {W2 : ℕ} (hvia : ViaFree V G a W2) : ∀ (L : List StripSpec) (σ : StripSpec),
    CRChain V G σ L → CATail (σ :: L) → EndOK V G σ →
    (∀ j < a.n, ∀ y ∈ cellE (endCell σ), y ∉ cellE (cellJ a.c a.s j)) →
    (∀ τ ∈ L, ¬ Touches a τ) → a.n + wt σ L ≤ W2 → FarChainCA G a σ L := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _ _; trivial
  | cons τ L' ih =>
    intro σ hch hnct hσ hσfar hnt hW
    obtain ⟨hσe, hl, hrest⟩ := hch
    obtain ⟨k, hk⟩ : ∃ k, a.n = k + 2 := ⟨a.n - 2, by omega⟩
    have ha' := ha
    obtain ⟨_, hpa, hca, hsep⟩ := ha'
    rw [hk] at hpa hca
    have hcell : ∀ j ≤ k + 1, IsCell V (cellJ a.c a.s j) := fun j hj => hca j (by omega)
    have hnτ := hnt τ (List.mem_cons_self ..)
    have hτ1 : 1 ≤ τ.n := hl.2.2.1
    obtain ⟨hu, lu1, lu2, _, _⟩ := hσ hσe
    have hmidτ : ∀ p, (∃ j < τ.n, ∃ x ∈ G, (x.p = p ∨ x.q = p) ∧ x ∈ cellE (cellJ τ.c τ.s j)) →
        ¬ IsMid a.c a.s (a.n - 2) p := by
      rintro p ⟨j, hj, x, hx, hxp, hxw⟩ hm
      rw [hk, show k + 2 - 2 = k by omega] at hm
      obtain ⟨i, hi, hxi⟩ := mid_touch hG hpa hcell hm hx hxp
      exact hnτ ⟨j, hj, i, by omega, x, hxw, hxi⟩
    have hmidσ : ∀ p (x : Edge), x ∈ G → (x.p = p ∨ x.q = p) → x ∈ cellE (endCell σ) →
        ¬ IsMid a.c a.s (a.n - 2) p := by
      intro p x hx hxp hxw hm
      rw [hk, show k + 2 - 2 = k by omega] at hm
      obtain ⟨i, hi, hxi⟩ := mid_touch hG hpa hcell hm hx hxp
      exact hσfar i (by omega) x hxw hxi
    -- The start corners of `τ` carry dark edges of `τ`, chain strip or not.
    --
    have hcorn : (back τ.c τ.s ∈ G ∧
        ((back τ.c τ.s).p = back1 τ.c τ.s ∨ (back τ.c τ.s).q = back1 τ.c τ.s) ∧
        back τ.c τ.s ∈ cellE (cellJ τ.c τ.s 0)) ∧
        ∃ j < τ.n, ∃ x ∈ G, (x.p = front1 τ.c τ.s ∨ x.q = front1 τ.c τ.s) ∧
          x ∈ cellE (cellJ τ.c τ.s j) := by
      by_cases hnc : NoChain σ τ
      · exact start_corner_edges ((pat_flip_off hτ1 hnc).1 hl.2.2.2.1) hτ1
      · obtain ⟨jy, hjy, y, hy, hyu⟩ : ∃ jy < τ.n, ∃ y ∈ cellE (cellJ τ.c τ.s jy),
            y ∈ cellE (endCell σ) := by
          by_contra hn; push Not at hn; exact hnc hn
        obtain ⟨rfl, -⟩ := hnct.1 jy hjy y hy hyu
        rw [cellJ_zero] at hy
        obtain ⟨_, _, hbG, hfr, _⟩ := chain_start hl hnct.1 ⟨lu1, lu2⟩ hy hyu
        exact chain_corner_edges hτ1 hbG hfr (chain_sig hl hnct.1)
    obtain ⟨⟨hb, hbp, hb0⟩, hfr⟩ := hcorn
    have mσ1 : lat1 (endCell σ) σ.s ∈ cellE (endCell σ) := by rw [cellE_frame _ σ.s]; simp
    have mσ2 : lat2 (endCell σ) σ.s ∈ cellE (endCell σ) := by rw [cellE_frame _ σ.s]; simp
    refine ⟨⟨hσfar, hmidσ _ _ lu1 ((ends_lat1 _ _).inc_iff _ |>.2 (Or.inl rfl)) mσ1,
      hmidσ _ _ lu2 ((ends_lat2 _ _).inc_iff _ |>.2 (Or.inl rfl)) mσ2,
      fun i hi j hj y hy hy' => hnτ ⟨i, hi, j, hj, y, hy, hy'⟩,
      hmidτ _ ⟨0, by omega, _, hb, hbp, hb0⟩, hmidτ _ hfr, ?_⟩, ?_⟩
    · rintro hnc ⟨hcg, hcu⟩
      have hpτ : StripPat G τ.c τ.s τ.n := (pat_flip_off hτ1 hnc).1 hl.2.2.2.1
      have hlink : CR2 V G a τ := link_a hG ha hae ha2 hτ1 hpτ hl.2.2.2.2.1 hnτ hcg hcu
      have hokA : ChainOK a τ := chainOK_of_noChain (fun j hj y hy hye =>
        hnτ ⟨j, hj, a.n - 1, by omega, y, hy, by unfold endCell at hye; exact hye⟩)
      refine hvia τ L' ⟨⟨ha, hae, hlink, hrest⟩, hokA, hnct.2⟩
        (fun x hx => hnt x (List.mem_cons_of_mem _ hx))
        (fun _ j hj y hy hy' => hnτ ⟨τ.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy,
          hy'⟩) ?_
      rw [wt_cons]; rw [wt_cons] at hW; have := hl.1; omega
    · refine ih τ hrest hnct.2 (endOK_of_link hl) (fun j hj y hy hy' => hnτ ⟨τ.n - 1, by omega,
        j, hj, y, hy, hy'⟩) (fun w hw => hnt w (List.mem_cons_of_mem _ hw))
        (by rw [wt_cons] at hW; omega)
end ULHC
