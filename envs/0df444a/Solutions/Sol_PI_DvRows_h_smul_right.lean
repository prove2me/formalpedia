-- Prove2me | solution 1 for PI.DvRows.h_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:13.901653+00:00
-- url     : https://prove2.me/submissions/81c81d29-0172-4a0d-b422-6cf78b7b7c1b

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
    h x (c • y) = algebraMap (𝓞 K) K c * h x y := by
  rw [← algebraMap_smul K c y, map_smul, smul_eq_mul]
end PI.DvRows
