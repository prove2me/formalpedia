-- Prove2me | solution 1 for WeierstrassEllipticZeta.nilpotent_kernel_local_residue_quotient
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T17:59:47.23369+00:00
-- url     : https://prove2.me/submissions/6ee9a83b-9466-4b6c-a3e5-95e2445550f2

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas



theorem solution
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (χ : A →ₐ[K] K) (hnil : ∀ a : A, χ a = 0 ↔ IsNilpotent a) :
    IsLocalRing A ∧ (nilradical A).IsMaximal ∧
      (∀ J : Ideal A, J.IsPrime ↔ J = nilradical A) ∧
      ∃ e : (A ⧸ nilradical A) ≃ₐ[K] K,
        ∀ a : A, e (Ideal.Quotient.mk (nilradical A) a) = χ a := by
  have hsurj : Function.Surjective χ := fun k =>
    ⟨algebraMap K A k, χ.commutes k⟩
  have hker : RingHom.ker χ = nilradical A := by
    ext a
    exact (hnil a).trans mem_nilradical.symm
  have hmax : (nilradical A).IsMaximal := by
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective χ hsurj
  have hprime : ∀ J : Ideal A, J.IsPrime ↔ J = nilradical A := by
    intro J
    constructor
    · intro hJ
      let := hJ
      exact (hmax.eq_of_le hJ.ne_top (nilradical_le_prime J)).symm
    · rintro rfl
      exact hmax.isPrime
  refine ⟨IsLocalRing.of_unique_max_ideal
    ⟨nilradical A, hmax, fun J hJ => (hprime J).mp hJ.isPrime⟩, hmax, hprime, ?_⟩
  rw [← hker]
  exact ⟨Ideal.quotientKerAlgEquivOfSurjective hsurj,
    fun a => Ideal.quotientKerAlgEquivOfSurjective_mk hsurj a⟩

