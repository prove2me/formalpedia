-- Prove2me | solution 1 for ULHC.round_ca
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:41:04.317027+00:00
-- url     : https://prove2.me/submissions/9bad5aa0-13d6-47a3-ae3b-2e922d52e10a

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_near_far_CA
import Theorems.Thm_ULHC_progress_step_CA


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
theorem _root_.solution {b : StripSpec} {L : List StripSpec} (hP : CRPathCA V G a (b :: L))
    (hWeq : W = wt a (b :: L)) :
    CRPathCA V (applyS G a) b L ∧ wt b L + a.n = wt a (b :: L) :=
  progress_step_CA hG hT ha hae ha2 hT' hP.1.2 hP.2
    (near_far_CA hs x0 hconn hG hT ha hae ha2 hT' hmin hP hWeq)
end ULHC
