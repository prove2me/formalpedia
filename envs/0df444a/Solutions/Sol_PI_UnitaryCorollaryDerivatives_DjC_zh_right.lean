-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.zh_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:25.66811+00:00
-- url     : https://prove2.me/submissions/1706f7de-52ee-49e7-abf9-63f4e78a3eb2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable (k j ρ : ℕ)
variable {k j ρ}
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution (g E : B.Mat k (j + ρ)) (hE : Pres (Set.range (eR k j ρ)) E) :
    Zh k j ρ (g * E) = Zh k j ρ g * sub (eR k j ρ) E := by
  ext a b
  have hr : 2 * (j + ρ) + k - a.val < 2 * (j + ρ) + k + 1 := by omega
  let r0 : Fin (2 * (j + ρ) + k + 1) := ⟨2 * (j + ρ) + k - a.val, hr⟩
  have key : (g * E) r0 (eR k j ρ b) = ∑ a', g r0 (eR k j ρ a') * E (eR k j ρ a') (eR k j ρ b) := by
    rw [Matrix.mul_apply, show (∑ a', g r0 (eR k j ρ a') * E (eR k j ρ a') (eR k j ρ b)) =
      ∑ m ∈ Finset.univ.map (eR k j ρ), g r0 m * E m (eR k j ρ b) from
      (Finset.sum_map Finset.univ (eR k j ρ) (fun m => g r0 m * E m (eR k j ρ b))).symm]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
    have hm' : m ∉ Set.range (eR k j ρ) := by
      rintro ⟨x, rfl⟩
      exact hm (Finset.mem_map_of_mem _ (Finset.mem_univ x))
    rw [hE m (eR k j ρ b) ⟨b, rfl⟩ hm', mul_zero]
  exact key
end PI.UnitaryCorollaryDerivatives.DjC
