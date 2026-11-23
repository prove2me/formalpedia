-- Prove2me | solution 1 for PIW.CMDiscSq.exists_of_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:38.178073+00:00
-- url     : https://prove2.me/submissions/522ccf3e-23ab-4099-9460-77254e486984

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_RelDiffTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_AdjoinEqTopOfStarNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open PIW PIW.CMDiscSq
namespace PIW.CMDiscSq
theorem _root_.solution {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {y : E} (hy : star y = y) :
    ∃ a : F, algebraMap F E a = y := by
  have : y ∈ Set.range (algebraMap F E) := by rw [hR]; exact hy
  exact this
end PIW.CMDiscSq
