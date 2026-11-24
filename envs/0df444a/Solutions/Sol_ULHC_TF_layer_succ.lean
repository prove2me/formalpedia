-- Prove2me | solution 1 for ULHC.TF.layer_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:10.198899+00:00
-- url     : https://prove2.me/submissions/d48fdd88-84c3-45a3-9d57-ef8fc02dfe1a

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution (V : Finset Pt) (F : Finset Edge) (k : ℕ) :
    layer V F (k + 1) = layer V F k ∪ (layer V F k).biUnion (nbr V F) := rfl
end ULHC.TF
