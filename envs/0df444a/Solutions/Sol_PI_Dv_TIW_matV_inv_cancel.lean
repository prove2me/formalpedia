-- Prove2me | solution 1 for PI.Dv.TIW.matV_inv_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:57.686788+00:00
-- url     : https://prove2.me/submissions/24f6d8ab-80db-4b11-96b5-2ed3146eb490

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Theorems.Thm_PI_Dv_TIW_matV_mul
import Theorems.Thm_PI_Dv_TIW_matV_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (x : n → V) :
    matV A (matV A⁻¹ x) = x := by
  rw [← LinearMap.comp_apply, ← matV_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), matV_one,
    LinearMap.id_apply]
end PI.Dv.TIW
