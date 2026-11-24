-- Prove2me | solution 1 for ULHC.Ends.swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:58.258012+00:00
-- url     : https://prove2.me/submissions/3840af73-4184-47f2-8b46-fd29acee4a61

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Ends
theorem _root_.solution {e : Edge} {u v : Pt} (h : Ends e u v) : Ends e v u := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h
end Ends
end ULHC
