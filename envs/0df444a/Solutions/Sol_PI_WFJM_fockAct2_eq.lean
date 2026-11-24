-- Prove2me | solution 1 for PI.WFJM.fockAct2_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:09.815654+00:00
-- url     : https://prove2.me/submissions/101ecef6-6cd1-4b8d-bbd5-7818394b37eb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix FockH1Action
namespace PI.WFJM
private theorem omAct_eq_sum_smul_omE (p q r s : ℕ)
    (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) :
    FockH1Action.omAct p q r s M = ∑ l, ∑ l', M l l' • FockH1Action.omE l l' := by
  first
  | (simp only [FockH1Action.omAct, LinearMap.sum_apply, LinearMap.smulRight_apply,
      Matrix.entryLinearMap_apply]; done)
  | simp [FockH1Action.omAct]
private theorem fockAct2_eq_omAct_one_kronecker (p q r s : ℕ) (Y : FockH1Action.Mat r s) :
    FockH1Action.fockAct2 p q r s Y =
      FockH1Action.omAct p q r s (Matrix.kroneckerMap (· * ·) (1 : FockH1Action.Mat p q) Y) := rfl
end PI.WFJM
namespace PI.WFJM
open MvPolynomial
open PI.FJM
section Grade
open MvPolynomial
variable {σ : Type*}
end Grade
section Lap
variable {p q r s : ℕ}
end Lap
section HW
variable {p q r s : ℕ}
open MvPolynomial
end HW
end PI.WFJM
namespace PI.FJM
end PI.FJM
end
end

set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
namespace PI.WFJM
theorem _root_.solution (p q r s : ℕ) (Y : Mat r s) :
    fockAct2 p q r s Y = ∑ a : Ix p q, ∑ c : Ix r s, ∑ d : Ix r s,
      Y c d • omE (p := p) (q := q) (r := r) (s := s) (a, c) (a, d) := by
  rw [fockAct2_eq_omAct_one_kronecker, omAct_eq_sum_smul_omE]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hb
    simp [Matrix.one_apply, Ne.symm hb]
end PI.WFJM
