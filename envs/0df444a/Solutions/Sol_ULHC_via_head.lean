-- Prove2me | solution 1 for ULHC.via_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:25:07.847286+00:00
-- url     : https://prove2.me/submissions/3d58cca5-cda1-4ceb-a9af-6f66cec3e3de

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_via_path
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_chainOK_of_noChain
import Theorems.Thm_ULHC_link_a


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0)
  (ha2 : 2 ≤ a.n) (hT' : NoTypeIII V (applyS G a))
include hs x0 hconn hG hT ha hae ha2 hT'
omit hs x0 hconn
namespace ULHC
theorem _root_.solution {q w : StripSpec} {L3 : List StripSpec} (hch : CRChain V G q (w :: L3))
    (hcat : CATail (q :: w :: L3)) (hntL : ∀ τ ∈ w :: L3, ¬ Touches a τ)
    (hpw : StripPat G w.c w.s w.n)
    (hsplit : ¬ Conn (flip G (endCell a)) (back1 w.c w.s) (front1 w.c w.s)) :
    ∃ σ L, CRPathCA V (applyS G a) σ L := by
  have hlw := hch.2.1
  have hnt := hntL w (List.mem_cons_self ..)
  have hw1 : 1 ≤ w.n := hlw.2.2.1
  have hlink : CR2 V G a w := link_a hG ha hae ha2 hw1 hpw hlw.2.2.2.2.1 hnt
    hlw.2.2.2.2.2.2.2.2.2.2.1 hsplit
  refine via_path hG hT ha hae ha2 hT' _ w L3
    ⟨⟨ha, hae, hlink, hch.2.2⟩, chainOK_of_noChain (fun jw hjw y hy hye => hnt ⟨jw, hjw,
      a.n - 1, by omega, y, hy, by unfold endCell at hye; exact hye⟩), hcat.2⟩ rfl
    (fun x hx => hntL x (List.mem_cons_of_mem _ hx))
    (fun _ j hj y hy hy' => hnt ⟨w.n - 1, by omega, j, hj, y, by unfold endCell at hy; exact hy,
      hy'⟩)
end ULHC
