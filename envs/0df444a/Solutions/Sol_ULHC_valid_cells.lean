-- Prove2me | solution 1 for ULHC.valid_cells
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:11:00.321802+00:00
-- url     : https://prove2.me/submissions/66482068-5271-4add-b3e6-6cb99fe2a9ac

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution {σ : StripSpec} (h : ValidStrip V G σ) :
    1 ≤ σ.n ∧ ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j) := by
  obtain ⟨h1, _, hc, _⟩ := h
  exact ⟨h1, hc⟩
end ULHC
