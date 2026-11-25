-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hTX5_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:03:17.211804+00:00
-- url     : https://prove2.me/submissions/1fe7ee11-7465-4371-992d-b98fd0797481

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_torusMean_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gaussAbs_rename_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K : Type} [Field K] [NumberField K] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (e : κ → κ') (he : Function.Injective e) (f : MvPolynomial κ K) :
    hTX5 (MvPolynomial.rename e f) = hTX5 f := by
  unfold hTX5
  congr 2
  · exact finsum_congr fun w => by rw [gaussAbs_rename_of_injective e he w f]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [MvPolynomial.map_rename, torusMean_rename e he]
end ReciprocityTheory.ChartRestriction.G.T0
