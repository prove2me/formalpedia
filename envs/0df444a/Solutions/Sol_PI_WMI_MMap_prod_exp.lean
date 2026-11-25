-- Prove2me | solution 1 for PI.WMI.MMap.prod_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:50.678104+00:00
-- url     : https://prove2.me/submissions/3b6a135d-ecd9-4997-9469-58054afafbc8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
open PI.WMI.MMap
namespace PI.WMI.MMap
theorem _root_.solution {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (θ : Fin N → ℝ) :
    ∏ v : Fin N × Fin N, Complex.exp ((θ v.2 : ℂ) * Complex.I) ^ m v =
      Complex.exp (((∑ v : Fin N × Fin N, (m v : ℝ) * θ v.2 : ℝ) : ℂ) * Complex.I) := by
  simp_rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => by ring
end PI.WMI.MMap
