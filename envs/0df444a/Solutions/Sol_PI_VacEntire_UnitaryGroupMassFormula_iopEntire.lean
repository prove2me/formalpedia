-- Prove2me | solution 1 for PI.VacEntire.UnitaryGroupMassFormula.iopEntire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:23:10.146022+00:00
-- url     : https://prove2.me/submissions/012a3348-232d-4d19-81ed-f4a1cd1186ea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VacEntire
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_VacuumEntire_AnalyticAtHfLeft
import Theorems.Thm_PI_VacEntire_UnitaryGroupMassFormula_analyticAt_U

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VacEntire PI.VacEntire.UnitaryGroupMassFormula
open PI.VacEntire
namespace PI.VacEntire.UnitaryGroupMassFormula
theorem _root_.solution : IopEntire := by
  intro ι _ N N' d A La₁ La₂ G hG c _
  by_cases h0 : (La₁.addSubgroupOf La₂).index = 0
  · have hfun : Iop d A La₁ La₂ G = fun _ => (0 : ℂ) := by
      funext z
      simp [Iop, h0]
    rw [hfun]
    exact analyticAt_const
  · have : Finite (La₂ ⧸ La₁.addSubgroupOf La₂) :=
      (AddSubgroup.index_ne_zero_iff_finite).1 h0
    let _ : Fintype (La₂ ⧸ La₁.addSubgroupOf La₂) := Fintype.ofFinite _
    have hfun : Iop d A La₁ La₂ G = fun z =>
        ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
          ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂,
            al d A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) *
              U A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) G z := by
      funext z
      simp only [Iop]
      rw [finsum_eq_sum_of_fintype]
    rw [hfun]
    refine analyticAt_const.mul ?_
    refine Finset.analyticAt_fun_sum _ (fun q _ => ?_)
    exact analyticAt_const.mul (analyticAt_U A _ G hG c)
end PI.VacEntire.UnitaryGroupMassFormula
