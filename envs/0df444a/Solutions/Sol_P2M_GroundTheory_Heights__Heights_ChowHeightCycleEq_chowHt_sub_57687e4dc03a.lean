-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_chowHt_sub_57687e4dc03a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:22.337794+00:00
-- url     : https://prove2.me/submissions/bcebb784-44f9-46f2-8309-5a66d9a96655

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowHeightCycleEq
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (μ ν : InfinitePlace K → Measure (Fin (e + 1) × Fin n → ℂ))
    (P : MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ P δ - ReciprocityTheory.ChartRestriction.G.Geo.chowHt ν P δ =
      (∑ w : InfinitePlace K, (w.mult : ℝ) *
        (ReciprocityTheory.ChartRestriction.G.Geo.logMean (μ w) (map w.embedding P) -
          ReciprocityTheory.ChartRestriction.G.Geo.logMean (ν w) (map w.embedding P))) / Height.totalWeight K := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.chowHt ReciprocityTheory.ChartRestriction.G.Geo.chowHeightOfForm
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring
end GroundTheory.Heights₂.Heights.ChowHeightCycleEq
