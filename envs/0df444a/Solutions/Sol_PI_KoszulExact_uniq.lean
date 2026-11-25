-- Prove2me | solution 1 for PI.KoszulExact.uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:10.636145+00:00
-- url     : https://prove2.me/submissions/19cfe51b-e266-4293-a2cb-bb918633e752

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ProjKillsLiPow
import Theorems.Thm_PI_KoszulExact_proj_kills_Li_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}
namespace PI.KoszulExact
theorem _root_.solution (i : Fin D) (p q : ℕ) (u v : ExteriorAlgebra R (Fin D → R))
    (hu : u ∈ Li R D i ^ p) (hv : v ∈ Li R D i ^ q) (h : u + eb R i * v = 0) : v = 0 ∧ u = 0 := by
  have h1 := congrArg (CliffordAlgebra.contractLeft (LinearMap.proj i : (Fin D → R) →ₗ[R] R)) h
  rw [map_add, map_zero, proj_kills_Li_pow i p u hu, zero_add, eb,
    CliffordAlgebra.contractLeft_ι_mul, ← eb, proj_kills_Li_pow i q v hv, mul_zero, sub_zero] at h1
  simp only [LinearMap.coe_proj, Function.eval, Pi.single_eq_same, one_smul] at h1
  refine ⟨h1, ?_⟩
  rw [h1, mul_zero, add_zero] at h
  exact h
end PI.KoszulExact
