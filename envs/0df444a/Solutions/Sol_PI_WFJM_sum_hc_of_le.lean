-- Prove2me | solution 1 for PI.WFJM.sum_hc_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:39.602382+00:00
-- url     : https://prove2.me/submissions/3f09c208-b780-432b-bb77-755ed1786991

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
open MvPolynomial
variable {σ : Type*}
namespace PI.WFJM
theorem _root_.solution (P : MvPolynomial σ ℂ) (n : ℕ) (hn : P.totalDegree < n) :
    ∑ i ∈ Finset.range n, homogeneousComponent i P = P := by
  have hx : ∑ i ∈ Finset.range (P.totalDegree + 1), homogeneousComponent i P = P := by
    first
    | exact sum_homogeneousComponent P
    | exact sum_homogeneousComponent
  calc ∑ i ∈ Finset.range n, homogeneousComponent i P
      = ∑ i ∈ Finset.range (P.totalDegree + 1), homogeneousComponent i P := by
        symm
        apply Finset.sum_subset
        · intro i hi
          simp only [Finset.mem_range] at hi ⊢
          omega
        · intro i _ hi
          simp only [Finset.mem_range, not_lt] at hi
          exact homogeneousComponent_eq_zero i P (by omega)
    _ = P := hx
end PI.WFJM
