-- Prove2me | solution 1 for ULHC.endCell_isCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:21:39.367435+00:00
-- url     : https://prove2.me/submissions/01d8ae6d-c7da-4fec-922d-61528e11e8e1

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution {σ : StripSpec} (h1 : 1 ≤ σ.n)
    (hc : ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j)) : IsCell V (endCell σ) :=
  hc (σ.n - 1) (by omega)
end ULHC
