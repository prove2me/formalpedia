-- Prove2me | solution 1 for PI.FockOneDegW.Swap.isHW_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:00.367983+00:00
-- url     : https://prove2.me/submissions/2fb64390-b747-46f3-ac1e-35fa1bc32103

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Theorems.Thm_PI_FockOneDegW_Swap_mem_hwSub_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
variable {m n : ℕ} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
namespace PI.FockOneDegW.Swap
theorem _root_.solution (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (act' : Mat m n →ₗ[ℂ] Module.End ℂ V')
    (e : V →ₗ[ℂ] V') (he : Function.Injective e) (hint : ∀ X w, act' X (e w) = e (act X w))
    (ν : Ix m n → ℚ) (w : V) (h : IsHW act' ν (e w)) : IsHW act ν w := by
  obtain ⟨h0, hmem⟩ := h
  refine ⟨fun h' => h0 (by rw [h', map_zero]), ?_⟩
  rw [mem_hwSub_iff] at hmem ⊢
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · apply he
    rw [← hint, hmem.1 a, map_smul]
  · apply he
    rw [← hint, hmem.2 a b hab, map_zero]
end PI.FockOneDegW.Swap
