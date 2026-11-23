-- Prove2me | solution 1 for PI.IsoDetW.Loc.algebraMap_mem_cI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:40.715553+00:00
-- url     : https://prove2.me/submissions/58346d11-6532-4f50-ba51-72036364dfa8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Theorems.Thm_PI_IsoDetW_Loc_mem_cI

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
theorem _root_.solution {J : Ideal R} {y : R} : algebraMap R K y ∈ cI K J ↔ y ∈ J := by
  rw [mem_cI]
  constructor
  · rintro ⟨z, hz, he⟩
    rwa [← (IsFractionRing.injective R K) he]
  · intro h; exact ⟨y, h, rfl⟩
end PI.IsoDetW.Loc
