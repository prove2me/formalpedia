-- Prove2me | solution 1 for ULHC.TF.no_edge_black
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:47:14.186851+00:00
-- url     : https://prove2.me/submissions/3a15d207-48e8-4479-b9d3-0cf63624eda0

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_black_q

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {S : Finset Pt} (hS : ∀ z ∈ S, Black z) (e : Edge) :
    ¬ (e.p ∈ S ∧ e.q ∈ S) := fun h => (black_q e).1 (hS _ h.2) (hS _ h.1)
end ULHC.TF
