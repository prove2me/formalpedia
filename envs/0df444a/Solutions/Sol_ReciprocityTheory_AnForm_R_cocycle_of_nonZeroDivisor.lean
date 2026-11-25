-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.cocycle_of_nonZeroDivisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:36.321543+00:00
-- url     : https://prove2.me/submissions/7183f238-a637-4be4-9c5c-bffa08c99f2b

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WCharts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {Ri Rj O : Type*} [CommRing Ri] [CommRing Rj] [CommRing O]
    (ri : Ri →+* O) (rj : Rj →+* O) {Gi Gj Gk tij tik : Ri} {Gj' Gk' tjk : Rj} {Oj Ok : O}
    (h1 : Gj = tij * Gi) (h2 : Gk = tik * Gi) (h3 : Gk' = tjk * Gj')
    (e1 : ri Gj = Oj) (e2 : rj Gj' = Oj) (e3 : ri Gk = Ok) (e4 : rj Gk' = Ok)
    (hG : ri Gi ∈ nonZeroDivisors O) : rj tjk * ri tij = ri tik := by
  have h5 : rj tjk * (ri tij * ri Gi) = ri tik * ri Gi := by
    rw [← map_mul, ← h1, e1, ← e2, ← map_mul, ← h3, e4, ← e3, h2, map_mul]
  have key : (rj tjk * ri tij - ri tik) * ri Gi = 0 := by
    rw [sub_mul, mul_assoc, h5, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hG).2 _ key)
end ReciprocityTheory.AnForm.R
