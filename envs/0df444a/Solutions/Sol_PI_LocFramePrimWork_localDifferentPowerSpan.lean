-- Prove2me | solution 1 for PI.LocFramePrimWork.localDifferentPowerSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:40.887706+00:00
-- url     : https://prove2.me/submissions/a9bc7593-05c3-4d98-a0e7-b724e0310ef3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_OEv
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_sc_eq
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_span_pow
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_neg

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
namespace PI.LocFramePrimWork
theorem _root_.solution : DiffLoc := by
  intro F E _ _ _ _ _ v k y
  change y ∈ DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    Set E) ↔ _
  rw [DiffLoc_neg, DiffLoc_span_pow, Submodule.mem_span_singleton_mul]
  have hsc : sc (E := E) v ((dV v)⁻¹ ^ k) = sc (E := E) v (dV v)⁻¹ ^ k := by
    rw [DiffLoc_sc_eq, DiffLoc_sc_eq, map_pow]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (DiffLoc_OEv v p).2 hp, by rw [hsc]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (DiffLoc_OEv v p).1 hp, by rw [hsc]⟩
end PI.LocFramePrimWork
