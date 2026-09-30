-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_cyclic_centralizer_algebra
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T22:59:55.969405+00:00
-- url     : https://prove2.me/submissions/3bbfd16b-445c-438d-8fee-2cf3cbe0de06

import Theorems.Thm_WeierstrassEllipticZeta_polynomial_cyclic_commutant
import Mathlib.Algebra.Algebra.Subalgebra.Basic



theorem solution
    (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
    (x : A)
    (hx : Function.Surjective (fun q : Polynomial R => q.eval₂ (algebraMap R A) x)) :
    ∃! e : A ≃ₐ[R] Subalgebra.centralizer R
        ({Algebra.lmul R A x} : Set (Module.End R A)),
      ∀ a : A, (e a : Module.End R A) = Algebra.lmul R A a := by
  let C := Subalgebra.centralizer R ({Algebra.lmul R A x} : Set (Module.End R A))
  have hmem (a : A) : Algebra.lmul R A a ∈ C := by
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    ext b
    exact mul_left_comm x a b
  let F : A →ₐ[R] C := (Algebra.lmul R A).codRestrict C hmem
  have hinj : Function.Injective F := by
    intro a b hab
    exact Algebra.lmul_injective (congrArg Subtype.val hab)
  have hsurj : Function.Surjective F := by
    intro T
    have hT := T.property (Algebra.lmul R A x) (Set.mem_singleton _)
    have hcomm : ∀ a : A,
        (T : Module.End R A) (x * a) = x * (T : Module.End R A) a := by
      intro a
      exact (congrArg (fun f : Module.End R A => f a) hT).symm
    obtain ⟨b, hb, _⟩ :=
      (WeierstrassEllipticZeta.polynomial_cyclic_commutant R A x hx
        (T : Module.End R A)).mp hcomm
    exact ⟨b, Subtype.ext hb.symm⟩
  let e : A ≃ₐ[R] C := AlgEquiv.ofBijective F ⟨hinj, hsurj⟩
  refine ⟨e, (fun _ => rfl), ?_⟩
  intro e' he'
  apply AlgEquiv.ext
  intro a
  exact Subtype.ext (he' a)

