-- Prove2me | solution 1 for PI.Dv.ProjAW.part2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:55.612085+00:00
-- url     : https://prove2.me/submissions/7b8067cb-43c9-4986-b649-9d023bcd92cb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
import Theorems.Thm_PI_Dv_ProjAW_mem_cutE
import Theorems.Thm_PI_Dv_ProjAW_mem_imgE
import Theorems.Thm_PI_Dv_ProjAW_idem_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution {f : Module.End K A.V} (hf : f * f = f) : cutE A f A.L ≤ imgE A f A.L := by
  intro x hx
  obtain ⟨hxL, hxr⟩ := (mem_cutE A f A.L x).1 hx
  exact (mem_imgE A f A.L x).2 ⟨x, hxL, idem_of A hf hxr⟩
end PI.Dv.ProjAW
