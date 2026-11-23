-- Prove2me | solution 1 for PI.Witt.expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:48.1958+00:00
-- url     : https://prove2.me/submissions/5040ccea-9354-4bc3-a9e4-bc029e2a0e4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_EnlargeStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]
namespace PI.Witt
theorem _root_.solution (B : V →ₗ⋆[K] V →ₗ[K] K) (p u u' : V) (c c' : K) :
    B (u + c • p) (u' + c' • p) =
      B u u' + c' * B u p + star c * B p u' + star c * c' * B p p := by
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply]
  generalize B u u' = A1
  generalize B u p = A2
  generalize B p u' = A3
  generalize B p p = A4
  generalize star c = s
  ring
end PI.Witt
