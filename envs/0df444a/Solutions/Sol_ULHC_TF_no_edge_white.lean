-- Prove2me | solution 1 for ULHC.TF.no_edge_white
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:47:18.985679+00:00
-- url     : https://prove2.me/submissions/d60fd8db-6d3d-4f0d-84e1-c2f615b94215

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_black_q

set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {S : Finset Pt} (hS : ∀ z ∈ S, ¬ Black z) (e : Edge) :
    ¬ (e.p ∈ S ∧ e.q ∈ S) := fun h => hS _ h.2 ((black_q e).2 (hS _ h.1))
end ULHC.TF
