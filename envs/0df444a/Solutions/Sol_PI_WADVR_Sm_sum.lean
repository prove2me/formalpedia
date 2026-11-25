-- Prove2me | solution 1 for PI.WADVR.Sm.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:12.734054+00:00
-- url     : https://prove2.me/submissions/e369b555-d7d0-4112-8347-a364cc7ecac7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeakApproxDVR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_RhoProjectionAssembly
import Theorems.Thm_PI_WADVR_Sm_add
import Theorems.Thm_PI_WADVR_Sm_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WADVR
namespace PI.WADVR
namespace Sm
theorem _root_.solution {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
    [Algebra W Q] [IsFractionRing W Q] {ϖ : W} {κ : Type*} (s : Finset κ) (f : κ → Q) (k : ℤ)
    (h : ∀ i ∈ s, Sm Q ϖ k (f i)) : Sm Q ϖ k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Sm.zero (Q := Q) (ϖ := ϖ) k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end Sm
end PI.WADVR
