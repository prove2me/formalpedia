-- Prove2me | solution 1 for ULHC.notouch_CA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:38:09.917632+00:00
-- url     : https://prove2.me/submissions/49a5c81b-d1c1-46e9-9d92-387518ea28cf

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_touch_contra_plain
import Theorems.Thm_ULHC_touch_contra_chain
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_endOK_of_link
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
theorem _root_.solution {W2 : ℕ} (hvia : ViaFree V G a W2) : ∀ (L : List StripSpec) (σ : StripSpec),
    CRChain V G σ L → CATail (σ :: L) → EndOK V G σ → wt σ L ≤ W → a.n + wt σ L ≤ W2 →
    ∀ τ ∈ L, ¬ Touches a τ := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _ τ h; simp at h
  | cons τ L' ih =>
    intro σ hch hnct hσ hW hW2
    obtain ⟨hσe, hl, hrest⟩ := hch
    have hfar2 := ih τ hrest hnct.2 (endOK_of_link hl) (by rw [wt_cons] at hW; omega)
      (by rw [wt_cons] at hW2; omega)
    have hW1' : wt τ L' < W := by rw [wt_cons] at hW; have := hl.1; omega
    have hW2' : a.n + wt τ L' < W2 := by rw [wt_cons] at hW2; have := hl.1; omega
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw'
    · by_cases hnc : NoChain σ w
      · exact touch_contra_plain hG hT ha hae ha2 hT' hmin hl hnc hσ hσe hrest
          hnct.2 hfar2 hvia hW1' hW2'
      · exact touch_contra_chain hs x0 hconn hG hT ha hae ha2 hT' hmin hl hnct.1 hnc hσ hσe
          hrest hnct.2 hfar2 hvia hW1' hW2'
    · exact hfar2 w hw'
end ULHC
