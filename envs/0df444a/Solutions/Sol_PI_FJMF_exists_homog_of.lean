-- Prove2me | solution 1 for PI.FJMF.exists_homog_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:17.556869+00:00
-- url     : https://prove2.me/submissions/c4d00545-94a9-4a47-a44f-f3fd979f05d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMF
variable {σ : Type*}
namespace PI.FJMF
theorem _root_.solution (P : MvPolynomial σ ℂ) (h0 : P ≠ 0) (D : ℚ)
    (h : ∀ e : ℕ, homogeneousComponent e P ≠ 0 → (e : ℚ) = D) :
    ∃ d : ℕ, (d : ℚ) = D ∧ P ∈ homog σ d := by
  have hex : ∃ e, homogeneousComponent e P ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h0
    rw [← sum_homogeneousComponent P]
    exact Finset.sum_eq_zero fun i _ => hall i
  obtain ⟨d, hd⟩ := hex
  refine ⟨d, h d hd, ?_⟩
  have hP : P = homogeneousComponent d P := by
    conv_lhs => rw [← sum_homogeneousComponent P]
    rw [Finset.sum_eq_single d]
    · intro i _ hi
      by_contra hne
      exact hi (by exact_mod_cast (h i hne).trans (h d hd).symm)
    · intro hdm
      exfalso
      apply hd
      apply homogeneousComponent_eq_zero
      rw [Finset.mem_range] at hdm
      omega
  rw [hP]
  exact homogeneousComponent_mem d P
end PI.FJMF
