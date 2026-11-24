-- Prove2me | solution 1 for ULHC.chainOK_far
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:15:33.215665+00:00
-- url     : https://prove2.me/submissions/cbce657d-9223-489b-a2b3-bedddb32e1c5

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Theorems.Thm_ULHC_chainOK_of_noChain


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {b τ : StripSpec}
    (h : ∀ j < τ.n, ∀ x ∈ cellE (cellJ τ.c τ.s j), x ∉ cellE (endCell b)) : ChainOK b τ :=
  chainOK_of_noChain h
end ULHC
