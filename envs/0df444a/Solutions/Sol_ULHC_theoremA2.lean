-- Prove2me | solution 1 for ULHC.theoremA2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:26:02.636542+00:00
-- url     : https://prove2.me/submissions/c01cc247-b1d4-43c3-a74a-6db7e3543525

import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq
import Theorems.Thm_ULHC_ValidSeqA_toValidSeq
import Theorems.Thm_ULHC_theoremA2_aux
import Theorems.Thm_ULHC_seq_count


set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam
namespace ULHC
theorem _root_.solution (F : Finset Edge) (hF : Deg2 V F) (h2 : 2 ≤ ncomp V F) :
    ∃ L : List StripSpec, ValidSeqA V none F L ∧ ncomp V (applySeq F L) + 1 = ncomp V F := by
  obtain ⟨L, hL⟩ := theoremA2_aux hs hH hHam _ F none rfl hF h2 trivial
  exact ⟨L, hL, seq_count L F hF (ValidSeqA.toValidSeq L none F hL)⟩
end ULHC
