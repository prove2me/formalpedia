-- Prove2me | solution 1 for TarchaBraids.presented_geom_relator_trace_eq_one_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T07:46:26.162693+00:00
-- url     : https://prove2.me/submissions/1dff285f-7d03-41e2-a058-f3c71eaa636b

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1
import Theorems.Thm_TarchaBraids_presented_relator_conjugate_eq_one_v1

open BraidsLinksMCG TarchaBraids

theorem solution {n : ℕ} {w : FreeGroup (Fin (n - 1))}
    (t : GeomRelatorTrace n w) :
    PresentedGroup.mk (braidRels n) w = 1 := by
  induction t with
  | nil => rfl
  | @step w u r t hr ih =>
      calc
        PresentedGroup.mk (braidRels n) (u * r * u⁻¹ * w) =
            PresentedGroup.mk (braidRels n) (u * r * u⁻¹) *
              PresentedGroup.mk (braidRels n) w := by
                simp only [PresentedGroup.mk, map_mul]
        _ = PresentedGroup.mk (braidRels n) w := by
                rw [presented_relator_conjugate_eq_one_v1 n u r hr, one_mul]
        _ = 1 := ih
