-- Prove2me | solution 1 for ULHC.near_far_CA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:39:37.31625+00:00
-- url     : https://prove2.me/submissions/e74bfa04-b012-4494-81f2-4e9c79bbbc98

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
import Theorems.Thm_ULHC_notouch_CA
import Theorems.Thm_ULHC_farchain_CA
import Theorems.Thm_ULHC_endOK_of_link
import Theorems.Thm_ULHC_wt_cons


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
    (hWeq : W = wt a (b :: L)) : FarChainCA G a b L := by
  obtain ⟨⟨_, _, hab, hch⟩, hcat⟩ := hP
  have hW : a.n + wt b L ≤ W := by rw [hWeq, wt_cons]
  have hvia0 : ViaFree V G a W := fun w R hP _ _ hlt => by have := hmin a (w :: R) hP; omega
  cases L with
  | nil => trivial
  | cons τ L' =>
    have hbe : b.n % 2 = 0 := hch.1
    have hbfar : ∀ j < a.n, ∀ y ∈ cellE (endCell b), y ∉ cellE (cellJ a.c a.s j) := by
      intro j hj y hy hy'
      by_cases hja : j + 1 < a.n
      · exact hab.2.2.2.2.2.1 (b.n - 1) (by have := hab.2.2.1; omega) j hja y hy hy'
      · exact hab.2.2.2.2.2.2.2.1 hbe y hy (by
          unfold endCell; rw [show a.n - 1 = j by omega]; exact hy')
    exact farchain_CA hG ha hae ha2 hvia0 (τ :: L') b hch hcat.2
      (endOK_of_link hab) hbfar
      (notouch_CA hs x0 hconn hG hT ha hae ha2 hT' hmin hvia0 (τ :: L') b hch hcat.2
        (endOK_of_link hab) (by omega) hW) hW
end ULHC
