-- Prove2me | solution 1 for PI.FockOneDegW.Swap.isHW_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:00.282084+00:00
-- url     : https://prove2.me/submissions/bfb4fd47-6f4b-44c8-99c9-9c9874e36f27

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
    (ν : Ix m n → ℚ) (w : V) (h : IsHW act ν w) : IsHW act' ν (e w) := by
  obtain ⟨h0, hmem⟩ := h
  refine ⟨fun h' => h0 (he (by rw [h', map_zero])), ?_⟩
  rw [mem_hwSub_iff] at hmem ⊢
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [hint, hmem.1 a, map_smul]
  · rw [hint, hmem.2 a b hab, map_zero]
end PI.FockOneDegW.Swap
