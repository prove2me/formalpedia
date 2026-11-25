-- Prove2me | solution 1 for PI.SqPair.LCP.plane_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:17.188726+00:00
-- url     : https://prove2.me/submissions/e121bc9a-b92b-46fa-99fd-d850becf9f32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PlaneIsUnitOfSubOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqPair PI.SqPair.LCP
open Polynomial IsLocalRing Matrix
namespace PI.SqPair.LCP
theorem _root_.solution {R : Type*} [CommRing R] (σ : R ≃+* R) (α β t s c : R)
    (hα : σ α = α) (h1 : β + t + σ t + t * σ t * α = 0)
    (h2 : s * (1 + t * α) + σ s * (1 + σ t * α) = -α) (h3 : c * (1 + t * α) = 1) :
    ((!![1 + s * t, c * t; s, c] : Matrix (Fin 2) (Fin 2) R).map σ)ᵀ * !![α, 1; 1, β]
        * !![1 + s * t, c * t; s, c] = !![0, 1; 1, 0] ∧
      (!![1 + s * t, c * t; s, c] : Matrix (Fin 2) (Fin 2) R).det = c := by
  have h3σ : σ c * (1 + σ t * α) = 1 := by
    have h4 := congrArg σ h3
    simpa only [map_mul, map_add, map_one, hα] using h4
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_one]
    · linear_combination h2 + σ s * s * h1
    · linear_combination h3 + σ s * c * h1
    · linear_combination h3σ + σ c * s * h1
    · linear_combination σ c * c * h1
  · simp [Matrix.det_fin_two]
    ring
end PI.SqPair.LCP
