-- Prove2me | solution 1 for PI.WAU.coord_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:14.95705+00:00
-- url     : https://prove2.me/submissions/ea7157a3-4ba1-4e1a-b546-8ea3e45bf89e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Theorems.Thm_PI_WAU_emb_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open scoped TensorProduct
variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
namespace PI.WAU
theorem _root_.solution : Function.Injective (coord b : E ⊗[F] B → ι → B) :=
  Function.LeftInverse.injective (emb_coord b)
end PI.WAU
