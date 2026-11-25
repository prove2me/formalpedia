-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemS_vol_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:38:40.021651+00:00
-- url     : https://prove2.me/submissions/f71cf9a3-e1b6-4cc0-8d7c-1966dc543388

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_detM_le

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
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) : volume (ZSpan.fundamentalDomain Y.b) ≤ 1 := by
  classical
  have hr : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    rw [Module.finrank_eq_card_basis Y.b, Fintype.card_fin]
  let b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι) :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℂ ι)).reindex (finCongr hr)
  rw [ZSpan.measure_fundamentalDomain Y.b volume b₀.toBasis]
  have h1 : volume (ZSpan.fundamentalDomain b₀.toBasis) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀.toBasis volume),
      OrthonormalBasis.coe_toBasis, b₀.volume_parallelepiped]
  rw [h1, mul_one]
  calc ENNReal.ofReal |b₀.toBasis.det Y.b| ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal (lemS_detM_le Y b₀)
    _ = 1 := ENNReal.ofReal_one
end ReciprocityTheory.ChartRestriction.G.I2
