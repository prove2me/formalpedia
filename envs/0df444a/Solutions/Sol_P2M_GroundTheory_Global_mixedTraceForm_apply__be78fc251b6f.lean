-- Prove2me | solution 1 for P2M_GroundTheory_Global_mixedTraceForm_apply__be78fc251b6f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:09.96809+00:00
-- url     : https://prove2.me/submissions/b21a5613-73f9-4a59-bc9c-c928e89a247e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (x y : mixedSpace K) :
    mixedTraceForm K x y = ∑ w, x.1 w * y.1 w + ∑ w, 2 * (x.2 w * y.2 w).re := rfl
end GroundTheory.Global
