-- Prove2me | solution 1 for PI.UD.circle_infinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:32:38.765791+00:00
-- url     : https://prove2.me/submissions/2fe0c74d-6bb7-48fe-b2d0-eef54ac02604

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_GramStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UD
namespace PI.UD
theorem _root_.solution : {z : ℂ | ‖z‖ = 1}.Infinite := by
  refine Set.Infinite.of_image Complex.re
    ((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono ?_)
  intro x hx
  have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  refine ⟨⟨x, Real.sqrt (1 - x ^ 2)⟩, ?_, rfl⟩
  show ‖(⟨x, Real.sqrt (1 - x ^ 2)⟩ : ℂ)‖ = 1
  rw [Complex.norm_def, Complex.normSq_mk, Real.mul_self_sqrt h1]
  simp [sq]
end PI.UD
