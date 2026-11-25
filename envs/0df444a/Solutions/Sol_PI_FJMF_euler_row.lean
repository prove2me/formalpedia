-- Prove2me | solution 1 for PI.FJMF.euler_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:15.474515+00:00
-- url     : https://prove2.me/submissions/e7e0efab-0f33-46e7-8809-c4c41d3d4fe4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
import Theorems.Thm_PI_WFJM_X_mul_pderiv_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PI PI.FJMF
variable {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ)
namespace PI.FJMF
theorem _root_.solution (a : Fin m) (c : ℕ) (P : MvPolynomial σ ℂ)
    (hP : ∀ e ∈ P.support, ∑ k : Fin n, e (ι (a, k)) = c) :
    ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (a, k)) P = (c : ℂ) • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, Finset.mul_sum, X_mul_pderiv_monomial]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.sum_smul, hP e he]
  exact (Nat.cast_smul_eq_nsmul ℂ c _).symm
end PI.FJMF
