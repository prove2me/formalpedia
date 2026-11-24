-- Prove2me | solution 1 for ULHC.chain_transfer_CA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:15.070178+00:00
-- url     : https://prove2.me/submissions/3a977c9b-8e5b-4f26-868f-cd46f94aadf1

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
import Theorems.Thm_ULHC_link_transfer_CA
import Theorems.Thm_ULHC_endOK_of_link


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
  {a : StripSpec} (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
  (hT' : NoTypeIII V (applyS G a))
include hG hT ha hae ha2 hT'
namespace ULHC
theorem _root_.solution : ∀ (L : List StripSpec) (σ : StripSpec),
    EndOK V G σ → CRChain V G σ L → CATail (σ :: L) → FarChainCA G a σ L →
      CRChain V (applyS G a) σ L := by
  intro L
  induction L with
  | nil => intro σ _ h _ _; exact h
  | cons τ L ih =>
    intro σ hσ hch hcat hfar
    obtain ⟨hev, hl, hrest⟩ := hch
    exact ⟨hev, link_transfer_CA hG hT ha hae ha2 hT' hσ hev hl hcat.1 hfar.1,
      ih τ (endOK_of_link hl) hrest hcat.2 hfar.2⟩
end ULHC
