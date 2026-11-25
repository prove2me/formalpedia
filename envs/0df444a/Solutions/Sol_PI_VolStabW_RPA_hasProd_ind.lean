-- Prove2me | solution 1 for PI.VolStabW.RPA.hasProd_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:26.924497+00:00
-- url     : https://prove2.me/submissions/15432d27-082d-4e72-85e2-be3692d95865

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
import Theorems.Thm_PI_VolStabW_RPA_hasProd_tl

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
theorem _root_.solution (hT : TailH m L) (S : Finset ι) :
    HasProd (({i | i ∉ S} : Set ι).mulIndicator (am m L)) (tl m L S) := by
  have h := hasProd_tl hT S
  exact hasProd_subtype_iff_mulIndicator.mp h
end PI.VolStabW.RPA
