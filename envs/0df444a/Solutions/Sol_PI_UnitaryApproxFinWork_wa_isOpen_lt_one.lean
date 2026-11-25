-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.wa_isOpen_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:29.303044+00:00
-- url     : https://prove2.me/submissions/2c55dd31-2adf-491c-9956-6399e01d36f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open PI PI.UnitaryApproxFinWork
variable {F : Type} [Field F] [NumberField F]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    IsOpen {y : v.adicCompletion F | Valued.v (y - x) < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [Valued.mem_nhds]
  refine ⟨1, fun z hz => ?_⟩
  have hz' : Valued.v (z - y) < 1 := by
    first
      | simpa using hz
      | exact_mod_cast hz
      | (simp only [Set.mem_setOf_eq, Units.val_one] at hz
         first
           | exact (Valuation.restrict_lt_iff _ _ _).mp hz
           | exact (Valuation.restrict_lt_one_iff _ _).mp hz
           | exact_mod_cast hz)
  simp only [Set.mem_setOf_eq] at hy ⊢
  have hzx : z - x = (z - y) + (y - x) := by abel
  rw [hzx]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hz' hy)
end PI.UnitaryApproxFinWork
