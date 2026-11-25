-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:31.218113+00:00
-- url     : https://prove2.me/submissions/170328b3-7b5c-4fdf-9b25-cc8d12d857c2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable (D : Dat A n r)
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (x x' y : n → A) : D.h (x - x') y = D.h x y - D.h x' y := by
  simp only [h, hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
end PI.VolSemiDirect.W.PG.Dat
