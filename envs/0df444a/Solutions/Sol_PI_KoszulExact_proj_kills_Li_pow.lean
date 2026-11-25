-- Prove2me | solution 1 for PI.KoszulExact.proj_kills_Li_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:04.160683+00:00
-- url     : https://prove2.me/submissions/bb979d1f-a8c0-4c4c-a632-ade902bf37aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ProjKillsLiPow
import Theorems.Thm_PI_KoszulExact_Li_eq_map
import Theorems.Thm_PI_KoszulExact_contract_pow_eq_zero


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
theorem _root_.solution (i : Fin D) (p : ℕ) (x : ExteriorAlgebra R (Fin D → R))
    (hx : x ∈ Li R D i ^ p) :
    CliffordAlgebra.contractLeft (LinearMap.proj i : (Fin D → R) →ₗ[R] R) x = 0 := by
  rw [Li_eq_map] at hx
  refine contract_pow_eq_zero _ _ ?_ p x hx
  intro m hm
  have hle : Submodule.span R ((fun k : Fin D => (Pi.single k (1 : R) : Fin D → R)) ''
      {k : Fin D | (k : ℕ) < i}) ≤ LinearMap.ker (LinearMap.proj i : (Fin D → R) →ₗ[R] R) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have hne : i ≠ k := fun h => by subst h; exact lt_irrefl (i : ℕ) hk
    simp [hne]
  exact hle hm
end PI.KoszulExact
