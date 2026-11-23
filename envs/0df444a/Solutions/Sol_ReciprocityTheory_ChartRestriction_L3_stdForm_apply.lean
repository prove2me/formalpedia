-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.stdForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:20.151217+00:00
-- url     : https://prove2.me/submissions/6e7c4c21-6732-4a75-9c83-888fde27a591

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
namespace ReciprocityTheory.ChartRestriction.L3
theorem _root_.solution (K : Type) [Field K] [StarRing K] (n : ℕ) (x y : Fin n → K) :
    stdForm K n x y = ∑ i, star (x i) * y i := rfl
end ReciprocityTheory.ChartRestriction.L3
