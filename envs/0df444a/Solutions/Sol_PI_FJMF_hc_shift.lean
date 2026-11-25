-- Prove2me | solution 1 for PI.FJMF.hc_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:21.838243+00:00
-- url     : https://prove2.me/submissions/1b31a8e1-e589-4223-a2f6-8c06024d0259

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
theorem _root_.solution (L : Module.End ℂ (MvPolynomial σ ℂ)) (k : ℕ)
    (hL : ∀ (d : ℕ) (Q : MvPolynomial σ ℂ), Q ∈ homog σ d → L Q ∈ homog σ (d + k))
    (j : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent j (L P) = if k ≤ j then L (homogeneousComponent (j - k) P) else 0 := by
  have hP := sum_homogeneousComponent P
  conv_lhs => rw [← hP]
  rw [map_sum, map_sum]
  have hterm : ∀ d, homogeneousComponent j (L (homogeneousComponent d P)) =
      if j = d + k then L (homogeneousComponent d P) else 0 := by
    intro d
    exact homogeneousComponent_of_mem (hL d _ (homogeneousComponent_mem d P))
  simp only [hterm]
  split_ifs with hkj
  · rw [Finset.sum_eq_single (j - k)]
    · rw [if_pos (by omega)]
    · intro d _ hd
      rw [if_neg (by omega)]
    · intro hm
      rw [if_pos (by omega)]
      rw [Finset.mem_range] at hm
      rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]
  · exact Finset.sum_eq_zero fun d _ => if_neg (by omega)
end PI.FJMF
