-- Prove2me | solution 1 for PI.FJMF.low_hc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:37.998372+00:00
-- url     : https://prove2.me/submissions/e84b59ea-de33-442e-a09b-1b64485b6f5c

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
theorem _root_.solution (L : Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) (h : L P = 0) (n : ℕ) : L (homogeneousComponent n P) = 0 := by
  have hz : ∀ e, homogeneousComponent e (L (homogeneousComponent n P)) = 0 := by
    intro e
    rw [hL e, homogeneousComponent_of_mem (homogeneousComponent_mem n P)]
    split_ifs with he
    · have h2 := hL e P
      rw [h, map_zero, he] at h2
      exact h2.symm
    · simp
  ext m
  have h3 := congrArg (coeff m) (hz (m.degree))
  rw [coeff_homogeneousComponent, if_pos rfl] at h3
  simpa using h3
end PI.FJMF
