-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.l2_ctU_eq_l2_ctY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:27:25.4239+00:00
-- url     : https://prove2.me/submissions/09f1e095-18b2-4274-a81e-a9004637ccfe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pointNormSq_translate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pointNormSq_periodic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_avg_trans

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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) (w : EuclideanSpace ℂ ι) {q : ℕ} {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ (ctY Y w).Sec q) :
    Y.l2 q (ctU q (-((1 / (q : ℂ)) • w)) F) = (ctY Y w).l2 q F := by
  have hper : ∀ γ ∈ lat Y.b, ∀ v, Y.ptN2 q F (v + γ) = Y.ptN2 q F v :=
    fun γ hγ v => pointNormSq_periodic (ctY Y w) hF hγ v
  simp only [GT.l2, pointNormSq_translate]
  exact ct_avg_trans Y _ hper _
end ReciprocityTheory.ChartRestriction.G.I2
