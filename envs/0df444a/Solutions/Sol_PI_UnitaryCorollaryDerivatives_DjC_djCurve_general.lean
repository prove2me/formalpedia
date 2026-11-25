-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.djCurve_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:45.411495+00:00
-- url     : https://prove2.me/submissions/03f1b3b6-1066-467b-99db-bd2e09d81556

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_det_sub_exp
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_trace_sub_le
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_presR
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_presL
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_zh_right
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_zh_left
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_pres_exp
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_pres_neg
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_pres_smul


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
theorem _root_.solution (Y : B.Mat k (j + ρ)) (hY : inLieP k j ρ Y) : ∃ c₁ c₂ : ℂ,
    ‖c₁‖ ≤ (j : ℝ) * mx Y ∧ ‖c₂‖ ≤ (j : ℝ) * mx Y ∧
    ∀ (g : B.Mat k (j + ρ)) (t : ℝ),
      DjU k j ρ (g * NormedSpace.exp ((t : ℂ) • Y)) = Complex.exp ((t : ℂ) * c₁) * DjU k j ρ g ∧
      DjU k j ρ (NormedSpace.exp (-((t : ℂ) • Y)) * g) = Complex.exp ((t : ℂ) * c₂) * DjU k j ρ g := by
  have hR := presR hY
  have hLp := presL hY
  have hmR : ∀ E F : B.Mat k (j + ρ), Pres (Set.range (eR k j ρ)) E → Pres (Set.range (eR k j ρ)) F →
      sub (eR k j ρ) (E * F) = sub (eR k j ρ) E * sub (eR k j ρ) F := by
    intro E F hE hF
    ext a b
    show ∑ m, E ((eR k j ρ) a) m * F m ((eR k j ρ) b) = ∑ a', E ((eR k j ρ) a) ((eR k j ρ) a') * F ((eR k j ρ) a') ((eR k j ρ) b)
    rw [← Finset.sum_map Finset.univ (eR k j ρ) (fun m => E ((eR k j ρ) a) m * F m ((eR k j ρ) b))]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
    have hm' : m ∉ Set.range (eR k j ρ) := by
      rintro ⟨x, rfl⟩
      exact hm (Finset.mem_map_of_mem _ (Finset.mem_univ x))
    rw [hF m ((eR k j ρ) b) ⟨b, rfl⟩ hm', mul_zero]
  have hmL : ∀ E F : B.Mat k (j + ρ), Pres (Set.range (eL k j ρ))ᶜ E → Pres (Set.range (eL k j ρ))ᶜ F →
      sub (eL k j ρ) (E * F) = sub (eL k j ρ) E * sub (eL k j ρ) F := by
    intro E F hE hF
    ext a b
    show ∑ m, E ((eL k j ρ) a) m * F m ((eL k j ρ) b) = ∑ a', E ((eL k j ρ) a) ((eL k j ρ) a') * F ((eL k j ρ) a') ((eL k j ρ) b)
    rw [← Finset.sum_map Finset.univ (eL k j ρ) (fun m => E ((eL k j ρ) a) m * F m ((eL k j ρ) b))]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_
    have hm' : m ∈ (Set.range (eL k j ρ))ᶜ := by
      rintro ⟨x, rfl⟩
      exact hm (Finset.mem_map_of_mem _ (Finset.mem_univ x))
    rw [hE ((eL k j ρ) a) m hm' (fun h => h ⟨a, rfl⟩), zero_mul]
  refine ⟨(sub (eR k j ρ) Y).trace, -(sub (eL k j ρ) Y).trace, trace_sub_le _ Y,
    by rw [norm_neg]; exact trace_sub_le _ Y, fun g t => ⟨?_, ?_⟩⟩
  · unfold DjU
    rw [zh_right g _ (pres_exp (pres_smul hR _)), Matrix.det_mul, det_sub_exp (eR k j ρ) _ Y hR hmR t, mul_comm]
  · unfold DjU
    have hneg : -((t : ℂ) • Y) = (t : ℂ) • (-Y) := (smul_neg _ _).symm
    rw [hneg, zh_left g _ (pres_exp (pres_smul (pres_neg hLp) _)), Matrix.det_mul,
      det_sub_exp (eL k j ρ) _ (-Y) (pres_neg hLp) hmL t]
    have htr : (sub (eL k j ρ) (-Y)).trace = -(sub (eL k j ρ) Y).trace := by
      rw [← Matrix.trace_neg]
      congr 1
    rw [htr]
end PI.UnitaryCorollaryDerivatives.DjC
