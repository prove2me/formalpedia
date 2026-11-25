-- Prove2me | solution 1 for PI.FJMF.low_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:40.567066+00:00
-- url     : https://prove2.me/submissions/c580ea45-c72e-4806-af62-9232ee99f1c3

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
theorem _root_.solution {ι : Type*} (t : Finset ι) (L : ι → Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ i (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L i P) = L i (homogeneousComponent (e + 2) P)) :
    ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e ((∑ i ∈ t, L i) P) = (∑ i ∈ t, L i) (homogeneousComponent (e + 2) P) := by
  intro e P
  simp only [LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => hL i e P
end PI.FJMF
