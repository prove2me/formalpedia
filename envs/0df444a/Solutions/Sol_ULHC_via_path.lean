-- Prove2me | solution 1 for ULHC.via_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:22:44.006572+00:00
-- url     : https://prove2.me/submissions/e851bac1-2b85-45ab-8f46-bdfa61070d5e

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_endOK_of_link
import Theorems.Thm_ULHC_farchain_CA
import Theorems.Thm_ULHC_progress_step_CA
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
include hs x0 hconn hG hT ha hae ha2 hT'
omit hs x0 hconn
namespace ULHC
theorem _root_.solution : ∀ (n : ℕ) (w : StripSpec) (R : List StripSpec), CRPathCA V G a (w :: R) →
    wt a (w :: R) = n → (∀ x ∈ R, ¬ Touches a x) →
    (R ≠ [] → ∀ j < a.n, ∀ y ∈ cellE (endCell w), y ∉ cellE (cellJ a.c a.s j)) →
    ∃ σ L, CRPathCA V (applyS G a) σ L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w R hP hwt hnt hfe
  by_contra hno
  have hvia : ViaFree V G a n := fun w' R' hP' hnt' hfe' hlt =>
    hno (ih _ hlt w' R' hP' rfl hnt' hfe')
  obtain ⟨⟨_, hch⟩, hcat⟩ := hP
  have hfar : FarChainCA G a w R := by
    cases R with
    | nil => trivial
    | cons τ R' =>
      exact farchain_CA hG ha hae ha2
        hvia (τ :: R') w hch.2.2 hcat.2 (endOK_of_link hch.2.1) (hfe (by simp)) hnt
        (by rw [← hwt, wt_cons a])
  exact hno ⟨w, R, (progress_step_CA hG hT ha hae ha2 hT' hch hcat hfar).1⟩
end ULHC
