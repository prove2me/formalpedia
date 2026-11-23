-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:36.926673+00:00
-- url     : https://prove2.me/submissions/4df207db-1611-4fae-bf9b-ae774ce249ad

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_left

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
theorem _root_.solution {ι : Type} (s : Finset ι) (x : ι → n → A) (y : n → A) :
    D.h (∑ i ∈ s, x i) y = ∑ i ∈ s, D.h (x i) y := by
  exact map_sum (AddMonoidHom.mk' (fun x => D.h x y) fun a b => D.h_add_left a b y) x s
end PI.VolSemiDirect.W.PG.Dat
