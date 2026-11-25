-- Prove2me | solution 1 for PI.FHS.conjTranspose_kronecker_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:26.694416+00:00
-- url     : https://prove2.me/submissions/22dfb179-5148-4386-b2a2-9deea2c6a148

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
theorem _root_.solution (Z : Mat p q) :
    (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s))ᴴ =
      Matrix.kroneckerMap (fun a b => a * b) Zᴴ (1 : Mat r s) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  by_cases hcd : c = d
  · subst hcd; simp
  · rw [Matrix.one_apply_ne hcd, Matrix.one_apply_ne (Ne.symm hcd)]; simp
end PI.FHS
