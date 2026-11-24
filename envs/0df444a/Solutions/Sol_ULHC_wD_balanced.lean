-- Prove2me | solution 1 for ULHC.wD_balanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:30.08208+00:00
-- url     : https://prove2.me/submissions/45c78601-f6be-4f58-921c-0234b472c5ad

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
import Theorems.Thm_ULHC_wD_balanced_at
import Theorems.Thm_ULHC_deg_eq_of_factors

set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
    (hF : IsFactor V d F) (hH : IsFactor V d H) : Balanced (wD F H) :=
  fun p => wD_balanced_at F H p (deg_eq_of_factors hF hH p)
end ULHC
