-- Prove2me | solution 1 for PI.WAU.ctsA_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:02.24671+00:00
-- url     : https://prove2.me/submissions/26a8786e-00a9-490b-85d7-e812cbf39206

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul

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
variable [TopologicalSpace B] [IsTopologicalRing B]
variable {b}
variable {X : Type*} [TopologicalSpace X]
namespace PI.WAU
theorem _root_.solution (y : E ⊗[F] B) : CtsA b (fun _ : X => y) := continuous_const
end PI.WAU
