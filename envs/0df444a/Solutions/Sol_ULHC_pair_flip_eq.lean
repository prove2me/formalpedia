-- Prove2me | solution 1 for ULHC.pair_flip_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:22:21.956364+00:00
-- url     : https://prove2.me/submissions/8826df3e-b143-4843-a118-ea831cccb82b

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_symmDiff_six
import Theorems.Thm_ULHC_pair_cells
import Theorems.Thm_ULHC_APair_flip


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} (c : Pt) (s : Side)
    (h1 : lat1 c s ∈ F) (h2 : lat2 c s ∈ F) (h3 : front (nb c s) s ∈ F)
    (h4 : back c s ∉ F) (h5 : lat1 (nb c s) s ∉ F) (h6 : lat2 (nb c s) s ∉ F) :
    flip (flip F (nb c s)) c = (mkPair c s).res F := by
  unfold flip
  rw [symmDiff_assoc, pair_cells]
  exact symmDiff_six h1 h2 h3 h4 h5 h6
end ULHC
