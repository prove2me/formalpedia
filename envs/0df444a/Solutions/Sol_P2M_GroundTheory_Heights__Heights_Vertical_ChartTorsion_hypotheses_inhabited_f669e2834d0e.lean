-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_hypotheses_inhabited_f669e2834d0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:58.855594+00:00
-- url     : https://prove2.me/submissions/6634134d-d619-4ae2-85d9-913104c37e76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace ChartTorsion
theorem _root_.solution :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℤ)).IsPrime ∧
      (∀ c : ℤ, C c ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℤ)) → c = 0) ∧
      C (1 : ℤ) * (0 : MvPolynomial (Fin 1 ⊕ (Fin 1 × Fin 1)) ℤ) ∈ incIdeal ⊥ 1 := by
  refine ⟨Ideal.isPrime_bot, fun c hc => ?_, by simp⟩
  rw [Ideal.mem_bot] at hc
  exact (C_eq_zero).mp hc
end ChartTorsion
end GroundTheory.Heights₂.Heights.Vertical
