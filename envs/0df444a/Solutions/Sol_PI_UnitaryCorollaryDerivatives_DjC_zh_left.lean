-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.zh_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:02.445488+00:00
-- url     : https://prove2.me/submissions/56eb7d0a-0d1b-4cf8-b953-96619b00c9b7

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
theorem _root_.solution (g E : B.Mat k (j + ρ)) (hE : Pres (Set.range (eL k j ρ))ᶜ E) :
    Zh k j ρ (E * g) = sub (eL k j ρ) E * Zh k j ρ g := by
  ext a b
  have hb : b.val < 2 * (j + ρ) + k + 1 := by omega
  let c0 : Fin (2 * (j + ρ) + k + 1) := ⟨b.val, hb⟩
  have key : (E * g) (eL k j ρ a) c0 = ∑ a', E (eL k j ρ a) (eL k j ρ a') * g (eL k j ρ a') c0 := by
    rw [Matrix.mul_apply, show (∑ a', E (eL k j ρ a) (eL k j ρ a') * g (eL k j ρ a') c0) =
      ∑ m ∈ Finset.univ.map (eL k j ρ), E (eL k j ρ a) m * g m c0 from
      (Finset.sum_map Finset.univ (eL k j ρ) (fun m => E (eL k j ρ a) m * g m c0)).symm]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
    have hm' : m ∈ (Set.range (eL k j ρ))ᶜ := by
      rintro ⟨x, rfl⟩
      exact hm (Finset.mem_map_of_mem _ (Finset.mem_univ x))
    rw [hE (eL k j ρ a) m hm' (fun h => h ⟨a, rfl⟩), zero_mul]
  exact key
end PI.UnitaryCorollaryDerivatives.DjC
