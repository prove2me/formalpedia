-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.mk_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:19.268727+00:00
-- url     : https://prove2.me/submissions/b740498e-213c-46d4-b4bf-6fbae34f5bf5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_CardRangeRedJ
import Theorems.Thm_PI_ParahoricIdxZ_W_mk_congr
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
theorem _root_.solution {a t : ℕ} (g : Formalism.DoubleCosetMeasures.GLint O (a + t)) {A : Matrix (Fin a) (Fin a) F}
    {B : Matrix (Fin a) (Fin t) F} {C : Matrix (Fin t) (Fin a) F} {D : Matrix (Fin t) (Fin t) F}
    (hg : ((g : GL (Fin (a + t)) F) : Matrix _ _ F) = theta A B C D) (x y : Fin a ⊕ Fin t)
    (hv : Matrix.fromBlocks A B C D x y ∈ O) :
    Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨((g : GL (Fin (a + t)) F) : Matrix _ _ F)
      (finSumFinEquiv x) (finSumFinEquiv y), g.2.1 _ _⟩ : O) =
      Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (⟨Matrix.fromBlocks A B C D x y, hv⟩ : O) :=
  mk_congr O ϖ hϖ _ _ (by rw [hg, theta_apply])
end PI.ParahoricIdxZ.W
