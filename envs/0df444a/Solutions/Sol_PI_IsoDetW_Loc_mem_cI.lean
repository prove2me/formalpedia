-- Prove2me | solution 1 for PI.IsoDetW.Loc.mem_cI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:11.946463+00:00
-- url     : https://prove2.me/submissions/4e42ff82-234c-429e-8aa2-74b0990bcaa7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
namespace PI.IsoDetW.Loc
theorem _root_.solution {J : Ideal R} {x : K} : x ∈ cI K J ↔ ∃ y ∈ J, algebraMap R K y = x := by
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
end PI.IsoDetW.Loc
