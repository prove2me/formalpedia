-- Prove2me | solution 1 for ULHC.ValidSeqA.toValidSeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:44:23.611539+00:00
-- url     : https://prove2.me/submissions/ffc6be03-66ec-455c-b915-aff48864f0e2

import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace ValidSeqA
theorem _root_.solution {V : Finset Pt} :
    ∀ (L : List StripSpec) (a : Option Pt) (F : Finset Edge), ValidSeqA V a F L → ValidSeq V F L
  | [], _, _, h => h.elim
  | [_], _, _, h => ⟨h.1, h.2.1⟩
  | _ :: τ :: L, _, _, h => ⟨h.1, h.2.1, h.2.2.1, solution (τ :: L) _ _ h.2.2.2.2⟩
end ValidSeqA
end ULHC
