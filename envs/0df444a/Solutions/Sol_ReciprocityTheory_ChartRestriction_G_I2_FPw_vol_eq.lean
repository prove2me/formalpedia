-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.vol_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:40:59.8669+00:00
-- url     : https://prove2.me/submissions/72518554-e29b-40e1-9913-1a8d907201c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_DetMEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_detM_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (Y : GT ι) : volume (ZSpan.fundamentalDomain Y.b) = 1 := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    first
      | (rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
          finrank_euclideanSpace])
      | simp [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι)]
  let b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι) :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℂ ι)).reindex (finCongr hfr)
  rw [ZSpan.measure_fundamentalDomain Y.b volume b₀.toBasis, detM_eq Y b₀,
    measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀.toBasis volume),
    OrthonormalBasis.coe_toBasis, b₀.volume_parallelepiped]
  simp
end ReciprocityTheory.ChartRestriction.G.I2.FPw
