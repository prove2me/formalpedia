-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.good_rowGen_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:47.241156+00:00
-- url     : https://prove2.me/submissions/5489920f-16a4-40d9-aa4e-158d9a66b766

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_good_zero
import Theorems.Thm_PI_OddDualWeyl_Hom_good_add
import Theorems.Thm_PI_OddDualWeyl_Hom_good_C
import Theorems.Thm_PI_OddDualWeyl_Hom_good_X_mul_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}
namespace PI.OddDualWeyl.Hom
theorem _root_.solution (a b : Fin k) (hδ : ∀ s, wt (a, s) = wt (b, s) + δ) (v : Fin k × Fin k) :
    Good wt δ (wt v) (rowGen R a b (X v)) := by
  simp only [rowGen, aeval_X]
  refine good_add (good_C (isWeightedHomogeneous_X R wt v)) ?_
  split_ifs with h
  · apply good_X_mul_C
    obtain ⟨v1, v2⟩ := v
    simp only at h ⊢
    subst h
    rw [← hδ]
    exact isWeightedHomogeneous_X R wt (a, v2)
  · exact good_zero _
end PI.OddDualWeyl.Hom
