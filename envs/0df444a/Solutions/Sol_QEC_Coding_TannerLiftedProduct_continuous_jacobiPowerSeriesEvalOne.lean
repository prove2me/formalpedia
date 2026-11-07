-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.continuous_jacobiPowerSeriesEvalOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:53:47.135379+00:00
-- url     : https://prove2.me/submissions/a5496eaa-a692-4174-be70-a7b35e5807d9

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    letI := JacobiTripleProductCore.piTop
    Continuous jacobiPowerSeriesEvalOne := by
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := JacobiTripleProductCore.piTop
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt,
    PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  change Filter.Tendsto
    (fun g : JacobiTripleProductCore.R =>
      jacobiLaurentEvalOne (PowerSeries.coeff n g))
    (nhds f)
    (nhds (jacobiLaurentEvalOne (PowerSeries.coeff n f)))
  exact (continuous_of_discreteTopology.comp
    (PowerSeries.WithPiTopology.continuous_coeff
      (LaurentPolynomial ℤ) n)).continuousAt
end QEC.Coding.TannerLiftedProduct
