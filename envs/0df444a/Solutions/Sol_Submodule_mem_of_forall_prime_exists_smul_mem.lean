-- Prove2me | solution 1 for Submodule.mem_of_forall_prime_exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/db4cbb6c-dd08-5250-9fa9-979e03f9bd0f

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_mem_of_forall_prime_exists_smul_mem

set_option autoImplicit false

theorem solution
    {V : Type*} [AddCommGroup V] (M : Submodule ℤ V) (x : V)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ∃ s : ℤ, ¬ (ℓ : ℤ) ∣ s ∧ s • x ∈ M) : x ∈ M := by
  let I : Ideal ℤ := M.comap (LinearMap.toSpanSingleton ℤ V x)
  have hI : ∀ n : ℤ, n ∈ I ↔ n • x ∈ M := fun n => by
    change LinearMap.toSpanSingleton ℤ V x n ∈ M ↔ _
    rw [LinearMap.toSpanSingleton_apply]
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal I).principal
  have hdI : ∀ n : ℤ, n ∈ I ↔ d ∣ n := fun n => by
    rw [hd]
    exact Ideal.mem_span_singleton
  by_cases h1 : d.natAbs = 1
  · have h1' : (1 : ℤ) ∈ I := (hdI 1).2 (Int.isUnit_iff_natAbs_eq.mpr h1).dvd
    have h1'' := (hI 1).1 h1'
    rwa [one_smul] at h1''
  · obtain ⟨ℓ, hℓp, hℓd⟩ := Int.exists_prime_and_dvd h1
    obtain ⟨s, hs, hsx⟩ := h ℓ.natAbs (Int.prime_iff_natAbs_prime.mp hℓp)
    exact (hs (Int.natAbs_dvd.mpr (hℓd.trans ((hdI s).1 ((hI s).2 hsx))))).elim

end S_Submodule_mem_of_forall_prime_exists_smul_mem
end P2MW
export P2MW.S_Submodule_mem_of_forall_prime_exists_smul_mem (solution)
