-- Prove2me | solution 1 for ULHC.chainOK_of_noChain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:00.897531+00:00
-- url     : https://prove2.me/submissions/154eea8c-f7e4-4a65-ba72-0ae672a5bae1

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks

set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {b c : StripSpec} (h : NoChain b c) : ChainOK b c :=
  fun j hj x hx hx' => absurd hx' (h j hj x hx)
end ULHC
