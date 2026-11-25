-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.red_eq_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:46.957334+00:00
-- url     : https://prove2.me/submissions/d98fbfcc-9b62-4b32-b74c-c3da7006a7d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_red_val
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
open Matrix Formalism.DoubleCosetMeasures.P.GLRed
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)
namespace PI.ParahoricIdxZ.W
theorem _root_.solution {a t : ℕ} (h : Formalism.DoubleCosetMeasures.GLint O (a + t))
    (A : Matrix (Fin a) (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) (B : Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))
    (C : Matrix (Fin t) (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) (D : Matrix (Fin t) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))
    (H : ∀ x y, Ideal.Quotient.mk _ (⟨((h : GL (Fin (a + t)) F) : Matrix _ _ F)
      (finSumFinEquiv x) (finSumFinEquiv y), h.2.1 _ _⟩ : O) = Matrix.fromBlocks A B C D x y) :
    ((red O (a + t) ϖ hϖ h : GL (Fin (a + t)) _) : Matrix _ _ _) = theta A B C D := by
  ext i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rw [red_val, theta_apply]
  exact H x y
end PI.ParahoricIdxZ.W
