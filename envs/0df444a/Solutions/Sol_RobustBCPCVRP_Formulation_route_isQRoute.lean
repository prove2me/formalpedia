-- Prove2me | solution 1 for RobustBCPCVRP.Formulation.route_isQRoute
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:19:34.789924+00:00
-- url     : https://prove2.me/submissions/294c4c92-77ad-4d10-be44-fa5a17ecf434

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
set_option autoImplicit false
open LysgaardCVRP.Shrink RobustBCPCVRP.Formulation

theorem solution {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (C : ℕ) (r : List (Fin (n + 1))) (hr : IsRoute E d C r) :
    IsQRoute E d C r := by
  obtain ⟨hw, hnd, hl⟩ := hr
  refine ⟨hw, ?_, hl⟩
  intro k hk heq
  have := (hnd.getElem_inj_iff (i := k) (j := k + 2)).1 heq
  omega
