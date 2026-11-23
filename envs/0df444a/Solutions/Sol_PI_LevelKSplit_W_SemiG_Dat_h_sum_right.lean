-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:28.604804+00:00
-- url     : https://prove2.me/submissions/4c291103-1953-40f6-86ae-d169cd7afc1a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable (D : Dat A n r)
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution {ι : Type} (s : Finset ι) (x : n → A) (y : ι → n → A) :
    D.h x (∑ i ∈ s, y i) = ∑ i ∈ s, D.h x (y i) := map_sum (D.hL x) y s
end PI.LevelKSplit.W.SemiG.Dat
