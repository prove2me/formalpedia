-- Prove2me | solution 1 for ULHC.progress_step_CA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:57.882375+00:00
-- url     : https://prove2.me/submissions/9446d60f-fb16-449a-baaf-e71a3651b3b7

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
import Theorems.Thm_ULHC_chain_transfer_CA
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_endOK_of_link
import Theorems.Thm_ULHC_link_step
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
  {a : StripSpec} (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
  (hT' : NoTypeIII V (applyS G a))
include hG hT ha hae ha2 hT'
namespace ULHC
theorem _root_.solution {b : StripSpec} {L : List StripSpec} (hch : CRChain V G a (b :: L))
    (hcat : CATail (a :: b :: L)) (hfar : FarChainCA G a b L) :
    CRPathCA V (applyS G a) b L ∧ wt b L + a.n = wt a (b :: L) := by
  obtain ⟨_, hl, hrest⟩ := hch
  refine ⟨⟨⟨link_step hG hT ha hl, chain_transfer_CA hG hT ha hae ha2 hT' L b (endOK_of_link hl)
    hrest hcat.2 hfar⟩, hcat.2⟩, ?_⟩
  simp [wt]; ring
end ULHC
