-- Prove2me | solution 1 for PI.VolStabSW.ChLiftW.addChar_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:53.577323+00:00
-- url     : https://prove2.me/submissions/0452bf0f-e466-4f92-a7d6-d065ea0300ef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensChLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open PI PI.VolStabSW
open PI.VolStabSW.ChLiftW
namespace PI.VolStabSW.ChLiftW
theorem _root_.solution {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  refine Finset.induction_on s (by simp [AddChar.map_zero_eq_one]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
end PI.VolStabSW.ChLiftW
