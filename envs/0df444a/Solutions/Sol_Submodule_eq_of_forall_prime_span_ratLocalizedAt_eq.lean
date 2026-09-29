-- Prove2me | solution 1 for Submodule.eq_of_forall_prime_span_ratLocalizedAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/78674c13-661c-53d6-bb9a-186cd6db8b52

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Rat
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_Submodule_mem_of_forall_prime_exists_smul_mem
import Theorems.Thm_Submodule_mem_span_ratLocalizedAt_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_eq_of_forall_prime_span_ratLocalizedAt_eq

set_option autoImplicit false

theorem solution
    {V : Type*} [AddCommGroup V] [Module ℚ V] (M N : Submodule ℤ V)
    (h : ∀ ℓ : ℕ, ℓ.Prime →
      Submodule.span (GaloisRep.ratLocalizedAt ℓ) (M : Set V) =
        Submodule.span (GaloisRep.ratLocalizedAt ℓ) (N : Set V)) : M = N := by
  apply le_antisymm
  · intro x hx
    apply Submodule.mem_of_forall_prime_exists_smul_mem
    intro ℓ hℓ
    rw [← Submodule.mem_span_ratLocalizedAt_iff N ℓ hℓ, ← h ℓ hℓ]
    exact Submodule.subset_span hx
  · intro x hx
    apply Submodule.mem_of_forall_prime_exists_smul_mem
    intro ℓ hℓ
    rw [← Submodule.mem_span_ratLocalizedAt_iff M ℓ hℓ, h ℓ hℓ]
    exact Submodule.subset_span hx

end S_Submodule_eq_of_forall_prime_span_ratLocalizedAt_eq
end P2MW
export P2MW.S_Submodule_eq_of_forall_prime_span_ratLocalizedAt_eq (solution)
