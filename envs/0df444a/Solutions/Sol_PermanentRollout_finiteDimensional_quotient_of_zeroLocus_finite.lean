-- Prove2me | solution 1 for PermanentRollout.finiteDimensional_quotient_of_zeroLocus_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/f78df628-1a89-42d6-bd0d-47e91d59f4d7

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_finiteDimensional_quotient_radical_of_zeroLocus_finite

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι]
    (I : Ideal (MvPolynomial ι ℂ))
    (hfinite : (MvPolynomial.zeroLocus ℂ I).Finite) :
    Module.Finite ℂ (MvPolynomial ι ℂ ⧸ I) := by
  classical
  let A := MvPolynomial ι ℂ ⧸ I
  let B := MvPolynomial ι ℂ ⧸ I.radical
  letI : Module.Finite ℂ B :=
    finiteDimensional_quotient_radical_of_zeroLocus_finite I hfinite
  let φ : A →ₐ[ℂ] B := Ideal.Quotient.factorₐ ℂ I.le_radical
  have hsurj : Function.Surjective φ :=
    Ideal.Quotient.factor_surjective I.le_radical
  have hnil : RingHom.ker φ.toRingHom ≤ nilradical A := by
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hp : p ∈ I.radical := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact ha
    obtain ⟨n, hn⟩ := hp
    rw [mem_nilradical]
    refine ⟨n, ?_⟩
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hn)
  exact Module.finite_of_surjective_of_ker_le_nilradical φ hsurj hnil
    (IsNoetherian.noetherian _)
end PermanentRollout
