-- Prove2me | solution 1 for Subalgebra.exists_forall_le_eq_of_monotone_of_le_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/774dd688-543f-53c6-9c46-10c37c856b94

import Mathlib
import Theorems.Thm_integralClosure_moduleFinite_of_isReduced_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_exists_forall_le_eq_of_monotone_of_le_integralClosure

set_option autoImplicit false

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [CommRing L] [IsReduced L] [Algebra K L] [Module.Finite K L]
    [Algebra R L] [IsScalarTower R K L]
    (D : ℕ → Subalgebra R L) (hmono : Monotone D) (hint : ∀ i, D i ≤ integralClosure R L) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → D i = D i₀ := by
  haveI : Module.Finite R ↥(integralClosure R L) := integralClosure.moduleFinite_of_isReduced_of_charZero R K L
  haveI : IsNoetherian R ↥(integralClosure R L) := inferInstance
  let N : ℕ →o Submodule R ↥(integralClosure R L) :=
    ⟨fun i => (Subalgebra.toSubmodule (D i)).comap (integralClosure R L).val.toLinearMap,
      fun i j hij x hx => hmono hij hx⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance N
  refine ⟨n, fun i hi => le_antisymm (fun x hx => ?_) (hmono hi)⟩
  have h1 : (⟨x, hint i hx⟩ : ↥(integralClosure R L)) ∈ N i := hx
  rw [← hn i hi] at h1
  exact h1

end S_Subalgebra_exists_forall_le_eq_of_monotone_of_le_integralClosure
end P2MW
export P2MW.S_Subalgebra_exists_forall_le_eq_of_monotone_of_le_integralClosure (solution)
