-- Prove2me | solution 1 for PI.WAU.ctsA_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:02.813478+00:00
-- url     : https://prove2.me/submissions/4cb9bd30-bfaf-48ed-97d1-3bb852848eb9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Theorems.Thm_PI_WAU_coord_emb

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
theorem _root_.solution {g : X → ι → B} (hg : Continuous g) : CtsA b (fun x => emb b (g x)) := by
  simpa [CtsA, coord_emb] using hg
end PI.WAU
