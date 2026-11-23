-- Prove2me | solution 1 for PI.LocLatSat.UnitaryGroupMassFormula.baseChange_apply_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:50.298036+00:00
-- url     : https://prove2.me/submissions/a2c95665-4d08-4eb7-8740-fe41cc1004f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open PI PI.LocLatSat PI.LocLatSat.UnitaryGroupMassFormula
variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}
omit [IsDedekindDomain R] [IsFractionRing R K]
namespace PI.LocLatSat.UnitaryGroupMassFormula
theorem _root_.solution (f : (Fin n → K) →ₗ[K] K) (x : Fin n → K) : fP φ f (bcG φ x) = φ (f x) := by
  have hx : x = ∑ k, x k • (fun j => if k = j then (1 : K) else 0) := by
    funext i
    simp [Finset.sum_apply]
  show ∑ k, φ (x k) * φ (f fun j => if k = j then 1 else 0) = φ (f x)
  conv_rhs => rw [hx]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul, map_mul]
end PI.LocLatSat.UnitaryGroupMassFormula
