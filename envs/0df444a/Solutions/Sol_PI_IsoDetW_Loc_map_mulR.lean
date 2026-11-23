-- Prove2me | solution 1 for PI.IsoDetW.Loc.map_mulR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:11.698442+00:00
-- url     : https://prove2.me/submissions/6e4c20b6-a5a3-41d8-9fec-c60df52edb63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_AlgebraMapMemCI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap

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
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
namespace PI.IsoDetW.Loc
theorem _root_.solution (a : K) (I : FI) :
    (I : Submodule R K).map (mulR a) = ((FractionalIdeal.spanSingleton _ a * I : FI) : Submodule R K) := by
  ext x
  simp only [Submodule.mem_map, FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul,
    LinearMap.coe_restrictScalars, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
end PI.IsoDetW.Loc
