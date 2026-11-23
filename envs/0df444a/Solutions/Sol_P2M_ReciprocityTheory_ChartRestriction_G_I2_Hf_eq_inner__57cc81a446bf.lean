-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_eq_inner__57cc81a446bf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:32.097998+00:00
-- url     : https://prove2.me/submissions/34b53c47-ad26-4002-8270-65c7abe733b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_Hf_eq_inner


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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type} [Fintype ι] (w v : EuclideanSpace ℂ ι) : Hf w v = inner ℂ v w :=
  lemS_Hf_eq_inner w v
end ReciprocityTheory.ChartRestriction.G.I2
