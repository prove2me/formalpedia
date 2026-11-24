-- Prove2me | solution 1 for ULHC.twoFactor_isSome_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:41:50.415448+00:00
-- url     : https://prove2.me/submissions/34e8bba3-64d1-4d42-a4bf-60d6e5787416

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_twoFactor_some
import Theorems.Thm_ULHC_twoFactor_none

set_option autoImplicit true
open ULHC
open Finset
open TF
namespace ULHC
theorem _root_.solution (V : Finset Pt) : (twoFactor V).isSome ↔ ∃ F, Deg2 V F := by
  constructor
  · intro h
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.1 h
    exact ⟨F, twoFactor_some hF⟩
  · intro h
    by_contra hn
    exact twoFactor_none (Option.not_isSome_iff_eq_none.1 hn) h
end ULHC
