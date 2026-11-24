-- Prove2me | solution 1 for ULHC.deg2_applySeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:20:35.336994+00:00
-- url     : https://prove2.me/submissions/15776797-0704-499b-9e26-5dd7ae0f43ef

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
import Theorems.Thm_ULHC_deg2_flipCol

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} :
    ∀ (L : List StripSpec) (F : Finset Edge), Deg2 V F → ValidSeq V F L → Deg2 V (applySeq F L) := by
  intro L
  induction L with
  | nil => intro F hF _; exact hF
  | cons σ L ih =>
    intro F hF hv
    rcases L with _ | ⟨τ, L⟩
    · exact deg2_flipCol σ.n F hF hv.1.2.1 hv.1.2.2.1
    · exact ih _ (deg2_flipCol σ.n F hF hv.1.2.1 hv.1.2.2.1) hv.2.2.2
end ULHC
