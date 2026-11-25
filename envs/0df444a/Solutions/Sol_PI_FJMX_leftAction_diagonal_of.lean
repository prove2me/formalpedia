-- Prove2me | solution 1 for PI.FJMX.leftAction_diagonal_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:59.719385+00:00
-- url     : https://prove2.me/submissions/66173cf3-c322-4483-8a69-faa7de64c6ed

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot

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
variable {p q r s : ℕ}
namespace PI.FJMX
theorem _root_.solution (hW : FormWt1) (P : Pol p q r s) (x : Ix p q) (W : ℤ)
    (h : ∀ m, coeff m P ≠ 0 → wt1 m x = W) :
    fockAct1 p q r s (Eab x x) P = ((((W : ℚ) + sh1 p q r s x : ℚ)) : ℂ) • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have e : monomial m (coeff m P) = coeff m P • monomial m (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, hW, h m (mem_support_iff.1 hm), smul_comm]
end PI.FJMX
