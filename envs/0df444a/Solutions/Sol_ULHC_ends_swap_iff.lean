-- Prove2me | solution 1 for ULHC.ends_swap_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:28:22.888805+00:00
-- url     : https://prove2.me/submissions/1d64e320-7c38-45ea-9f81-45363b772078

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_Ends_swap


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} (B : Finset Edge)
namespace ULHC
theorem _root_.solution {u v : Pt} : (∃ e ∈ B, Ends e u v) ↔ (∃ e ∈ B, Ends e v u) :=
  ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.swap⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.swap⟩⟩
end ULHC
