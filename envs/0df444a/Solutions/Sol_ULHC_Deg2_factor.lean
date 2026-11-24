-- Prove2me | solution 1 for ULHC.Deg2.factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:11.422806+00:00
-- url     : https://prove2.me/submissions/263c0307-c48f-4c7f-89f4-42adf068f01c

import Definitions.Def_ULHC_Walk
import Definitions.Def_ULHC_Phase

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Deg2
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (h : Deg2 V F) : IsFactor V (fun _ => 2) F :=
  ⟨fun e he => h.1 e he, h.2⟩
end Deg2
end ULHC
