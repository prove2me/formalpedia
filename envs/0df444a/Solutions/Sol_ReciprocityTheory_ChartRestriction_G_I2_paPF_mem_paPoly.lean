-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paPF_mem_paPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:26:09.849594+00:00
-- url     : https://prove2.me/submissions/8ec01f05-a430-4bc0-bf79-d18b4ad25aef

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_mem_paS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sum_eq_degree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPF_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paMono_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {c : ℕ} {p : MvPolynomial ι ℂ} (hp : p.totalDegree ≤ c) :
    paPF p ∈ paPoly c := by
  rw [paPF_eq_sum]
  refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (paMono_mem (mem_paS.2 ?_))
  have := MvPolynomial.le_totalDegree hm
  rw [sum_eq_degree] at this
  omega
end ReciprocityTheory.ChartRestriction.G.I2
