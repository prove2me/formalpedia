-- Prove2me | solution 1 for PI.WFJM.fockAct1_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:28.623144+00:00
-- url     : https://prove2.me/submissions/88111980-af9d-4043-aebb-a88ea0c0fe3b

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
private theorem fockAct1_eq_omAct_kronecker_one (p q r s : ℕ) (Z : FockH1Action.Mat p q) :
    FockH1Action.fockAct1 p q r s Z =
      FockH1Action.omAct p q r s (Matrix.kroneckerMap (· * ·) Z (1 : FockH1Action.Mat r s)) := rfl
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
theorem _root_.solution (p q r s : ℕ) (Z : Mat p q) :
    fockAct1 p q r s Z = ∑ a : Ix p q, ∑ b : Ix p q, ∑ c : Ix r s,
      Z a b • omE (p := p) (q := q) (r := r) (s := s) (a, c) (b, c) := by
  rw [fockAct1_eq_omAct_kronecker_one, omAct_eq_sum_smul_omE]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_eq_single c]
  · simp
  · intro d hd
    simp [Matrix.one_apply, Ne.symm hd]
end PI.WFJM
