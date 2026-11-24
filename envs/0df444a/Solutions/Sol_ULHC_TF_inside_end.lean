-- Prove2me | solution 1 for ULHC.TF.inside_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:46:12.05307+00:00
-- url     : https://prove2.me/submissions/95ddfb5f-e1de-473c-9a60-ea07d5fbc6ba

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {e : Edge} (he : IsEdge V e) {z : Pt} (hz : e.p = z ∨ e.q = z) :
    z ∈ V := by
  rcases hz with h | h <;> rw [← h]
  exacts [he.1, he.2]
end ULHC.TF
