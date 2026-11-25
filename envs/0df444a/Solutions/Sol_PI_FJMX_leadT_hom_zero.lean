-- Prove2me | solution 1 for PI.FJMX.leadT_hom_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:57.179797+00:00
-- url     : https://prove2.me/submissions/a6b9c583-0663-44cc-8a5c-bfd9acf7558b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Theorems.Thm_PI_FJMX_minorPolynomial_isWeightedHomogeneous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s m k : ℕ}
namespace PI.FJMX
theorem _root_.solution (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ)
    (hw : ∀ i j, w (ρ i, κ j) = 0) (t : ℕ) :
    IsWeightedHomogeneous w (leadT (varMat ρ κ) t) 0 := by
  unfold leadT
  split_ifs with hh
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun _ => 0) (fun _ => 0) (fun i j => by simp [hw])
    simp only [Finset.sum_const_zero, add_zero] at this
    exact this
  · exact isWeightedHomogeneous_zero _ _ _
end PI.FJMX
