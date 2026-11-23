-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ChA.Mc_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:35.567074+00:00
-- url     : https://prove2.me/submissions/939d31e6-c4da-40fc-9d33-62aec788a8da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.ChA
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.ChA
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) (i : Idx dim) :
    Mc σ c v i = if i.1 = σ then c * v i else
      if i.1 = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c * v i else 0 := rfl
end ReciprocityTheory.ChartRestriction.G.I2.ChA
