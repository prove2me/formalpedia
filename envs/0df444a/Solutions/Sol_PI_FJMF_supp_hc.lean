-- Prove2me | solution 1 for PI.FJMF.supp_hc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:26.119571+00:00
-- url     : https://prove2.me/submissions/227aee1f-31e4-4800-8fae-d9550ed66193

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
theorem _root_.solution {e : ℕ} {P : MvPolynomial σ ℂ} {m : σ →₀ ℕ}
    (h : m ∈ (homogeneousComponent e P).support) : m ∈ P.support := by
  rw [mem_support_iff, coeff_homogeneousComponent] at h
  rw [mem_support_iff]
  split_ifs at h
  · exact h
  · exact absurd rfl h
end PI.FJMF
