-- Prove2me | solution 1 for ULHC.even_strip_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:29:59.308624+00:00
-- url     : https://prove2.me/submissions/31a9cd12-c15a-49ad-a2f7-c2528e50037f

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_alt_corners_conn
import Theorems.Thm_ULHC_back_cellJ_succ
import Theorems.Thm_ULHC_lat1_eq
import Theorems.Thm_ULHC_lat2_eq
import Theorems.Thm_ULHC_strip_even
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {σ : StripSpec} (hF : Deg2 V F)
    (hT : NoTypeIII V F) (hv : ValidStrip V F σ) (hev : σ.n % 2 = 0) :
    ncomp V (applyS F σ) = ncomp V F := by
  obtain ⟨hn, hpat, hcell, hsep⟩ := hv
  obtain ⟨k, hk⟩ : ∃ k, σ.n = k + 2 := ⟨σ.n - 2, by omega⟩
  have hsame : Conn F (back1 (cellJ σ.c σ.s (k + 1)) σ.s) (back2 (cellJ σ.c σ.s (k + 1)) σ.s) := by
    rw [hk] at hpat hcell
    have hce := hcell (k + 1) (by omega)
    obtain ⟨_, hl, hf⟩ := hpat
    have ha : Alt F (cellJ σ.c σ.s (k + 1)) := by
      have l1 := (hl (k + 1) (by omega)).1.2 (by omega)
      have l2 := (hl (k + 1) (by omega)).2.2 (by omega)
      have fF : front (cellJ σ.c σ.s (k + 1)) σ.s ∉ F := by
        intro h; have := (hf (k + 1) (by omega)).1 h; omega
      have bF : back (cellJ σ.c σ.s (k + 1)) σ.s ∉ F := by
        rw [back_cellJ_succ]; intro h; have := (hf k (by omega)).1 h; omega
      rw [lat1_eq] at l1
      rw [lat2_eq] at l2
      simp only [back, front] at fF bF
      generalize cellJ σ.c σ.s (k + 1) = r at *
      obtain ⟨x, y⟩ := r
      cases hs : σ.s <;> rw [hs] at l1 l2 fF bF <;>
        simp only [latA, latB, sideEdge, Side.opp] at l1 l2 fF bF <;> unfold Alt <;> tauto
    obtain ⟨k1, k2, k3⟩ := alt_corners_conn hT hce ha
    generalize cellJ σ.c σ.s (k + 1) = r at *
    obtain ⟨x, y⟩ := r
    cases σ.s <;> simp only [back1, back2] at * <;>
      first
      | exact k1
      | exact k2.symm.trans k3
      | exact k1.symm.trans k3
      | exact k2
  unfold applyS
  rw [hk] at hpat hcell ⊢
  exact strip_even k (by omega) F hF (fun j hj => hcell j (by omega)) hpat hsep hsame
end ULHC
