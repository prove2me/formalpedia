-- Prove2me | solution 1 for PI.VolStabW.RPA.tl_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:05.809101+00:00
-- url     : https://prove2.me/submissions/f9a46d2d-ab17-4c28-9281-dee4e5d31c5f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
import Theorems.Thm_PI_VolStabW_RPA_tl_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RPA
open MeasureTheory Filter Finset
open scoped NNReal ENNReal
variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))
variable {m L}
namespace PI.VolStabW.RPA
theorem _root_.solution [DecidableEq ι] (hT : TailH m L) {S : Finset ι} {i : ι} (hi : i ∉ S)
    (h0 : am m L i = 0) : tl m L S = 0 := by
  rw [tl_split hT (Finset.subset_insert i S), Finset.prod_eq_zero (i := i) (by simp [hi]) h0, zero_mul]
end PI.VolStabW.RPA
