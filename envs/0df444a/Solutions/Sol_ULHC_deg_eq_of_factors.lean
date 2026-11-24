-- Prove2me | solution 1 for ULHC.deg_eq_of_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:01:47.014646+00:00
-- url     : https://prove2.me/submissions/bcaf2861-b568-4a22-b7be-36f146ca4b8d

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_deg_zero_of_not_mem

set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
    (hF : IsFactor V d F) (hH : IsFactor V d H) (p : Pt) : deg F p = deg H p := by
  by_cases hp : p ∈ V
  · rw [hF.2 p hp, hH.2 p hp]
  · rw [deg_zero_of_not_mem hF hp, deg_zero_of_not_mem hH hp]
end ULHC
