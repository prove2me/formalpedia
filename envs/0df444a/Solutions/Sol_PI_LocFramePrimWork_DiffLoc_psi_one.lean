-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_psi_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:14.362189+00:00
-- url     : https://prove2.me/submissions/5919549e-c1f0-4e77-848e-0790dd762a5b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution :
    DiffLoc_psi v ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) = DiffLoc_P (E := E) v := by
  unfold DiffLoc_P
  congr 1
  ext x
  exact (FractionalIdeal.mem_one_iff _).trans Iff.rfl
end PI.LocFramePrimWork
