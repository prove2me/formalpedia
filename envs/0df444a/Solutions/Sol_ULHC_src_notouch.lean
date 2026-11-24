-- Prove2me | solution 1 for ULHC.src_notouch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:39:36.796314+00:00
-- url     : https://prove2.me/submissions/71bdd03d-db34-4d11-9aee-1ec0cc8fc7bf

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_endOK_of_valid
import Theorems.Thm_ULHC_via_path
import Theorems.Thm_ULHC_Adj_symm
import Theorems.Thm_ULHC_Conn_symm
import Theorems.Thm_ULHC_PStep_symm
import Theorems.Thm_ULHC_notouch_CA


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
    (hWq : W = wt q L) (hno : ¬ ∃ σ L', CRPathCA V (applyS G a) σ L') : ∀ τ ∈ L, ¬ Touches a τ :=
  notouch_CA hs x0 hconn hG hT ha hae ha2 hT' hmin (W2 := a.n + wt q L)
    (fun w R hP' hnt hfe _ => hno (via_path hG hT ha hae ha2 hT' _ w R hP' rfl hnt hfe))
    L q hP.1.2 hP.2 (endOK_of_valid hP.1.1) (le_of_eq hWq.symm) le_rfl
end ULHC
