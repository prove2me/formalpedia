-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.theta_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:04:02.047122+00:00
-- url     : https://prove2.me/submissions/a380c1d9-2700-430e-86bd-e866519a640b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
import Theorems.Thm_PI_ParahoricIdxZ_W_theta_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
namespace PI.ParahoricIdxZ.W
theorem _root_.solution {a t : ℕ} {A : Matrix (Fin a) (Fin a) F} {B : Matrix (Fin a) (Fin t) F}
    {C : Matrix (Fin t) (Fin a) F} {D : Matrix (Fin t) (Fin t) F}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (hC : ∀ i j, C i j ∈ O)
    (hD : ∀ i j, D i j ∈ O) : Formalism.DoubleCosetMeasures.IsInt O (theta A B C D) := by
  unfold Formalism.DoubleCosetMeasures.IsInt
  intro i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rw [theta_apply]
  rcases x with x | x <;> rcases y with y | y <;> simp [hA, hB, hC, hD]
end PI.ParahoricIdxZ.W
