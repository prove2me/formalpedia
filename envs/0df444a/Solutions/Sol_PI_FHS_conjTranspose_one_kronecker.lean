-- Prove2me | solution 1 for PI.FHS.conjTranspose_one_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:53.975698+00:00
-- url     : https://prove2.me/submissions/3e28f108-cad1-4ba5-947f-e50fa60a38f1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {p q r s : ℕ}
namespace PI.FHS
theorem _root_.solution (Z : Mat r s) :
    (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z)ᴴ =
      Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Zᴴ := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab)]; simp
end PI.FHS
