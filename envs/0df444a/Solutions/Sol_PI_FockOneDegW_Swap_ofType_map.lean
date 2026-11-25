-- Prove2me | solution 1 for PI.FockOneDegW.Swap.ofType_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:11.000462+00:00
-- url     : https://prove2.me/submissions/16bcf574-45b1-4ec2-afef-034eafc69af9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Theorems.Thm_PI_FockOneDegW_Swap_isHW_of_map

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
    (μ : Ix m n → ℚ) (v : V) (h : OfType act μ v) : OfType act' μ (e v) := by
  obtain ⟨W, hW, hv, hK, hty⟩ := h
  refine ⟨W.map e, ?_, Submodule.mem_map_of_mem hv, ?_, ?_⟩
  · exact Module.Finite.map W e
  · intro X hX w' hw'
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hw'
    rw [hint]
    exact Submodule.mem_map_of_mem (hK X hX w hw)
  · intro ν w' hw' hhw
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hw'
    exact hty ν w hw (isHW_of_map act act' e he hint ν w hhw)
end PI.FockOneDegW.Swap
