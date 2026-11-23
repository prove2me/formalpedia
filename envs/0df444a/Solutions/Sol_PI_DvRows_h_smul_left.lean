-- Prove2me | solution 1 for PI.DvRows.h_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:57.30836+00:00
-- url     : https://prove2.me/submissions/087c1aec-0854-4597-9fac-0a2ae77ea0cd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) (x y : V) :
    h (c • x) y = star (algebraMap (𝓞 K) K c) * h x y := by
  rw [← algebraMap_smul K c x, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
end PI.DvRows
