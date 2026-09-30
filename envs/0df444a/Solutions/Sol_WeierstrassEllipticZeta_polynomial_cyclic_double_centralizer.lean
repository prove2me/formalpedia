-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_cyclic_double_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T23:33:23.710316+00:00
-- url     : https://prove2.me/submissions/7f9d12f3-a691-47ff-8266-35d3467c5a1c

import Theorems.Thm_WeierstrassEllipticZeta_polynomial_cyclic_centralizer_algebra
import Mathlib.RingTheory.Adjoin.Polynomial.Basic



theorem solution
    (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
    (x : A)
    (hx : Function.Surjective (fun q : Polynomial R => q.eval₂ (algebraMap R A) x)) :
    let C := Subalgebra.centralizer R
      ({Algebra.lmul R A x} : Set (Module.End R A))
    C = Algebra.adjoin R ({Algebra.lmul R A x} : Set (Module.End R A)) ∧
      Subalgebra.centralizer R (C : Set (Module.End R A)) = C := by
  let C := Subalgebra.centralizer R ({Algebra.lmul R A x} : Set (Module.End R A))
  obtain ⟨e, he, _⟩ :=
    WeierstrassEllipticZeta.polynomial_cyclic_centralizer_algebra R A x hx
  have hC : C = (Algebra.lmul R A).range := by
    ext T
    constructor
    · intro hT
      obtain ⟨a, ha⟩ := e.surjective ⟨T, hT⟩
      exact ⟨a, (he a).symm.trans (congrArg Subtype.val ha)⟩
    · rintro ⟨a, rfl⟩
      change Algebra.lmul R A a ∈ C
      rw [← he a]
      exact (e a).property
  have hgen : Algebra.adjoin R ({x} : Set A) = ⊤ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
    exact hx
  have hadjoin : Algebra.adjoin R ({Algebra.lmul R A x} : Set (Module.End R A)) =
      (Algebra.lmul R A).range := by
    rw [← (Algebra.lmul R A).map_adjoin_singleton x, hgen, Algebra.map_top]
  refine ⟨hC.trans hadjoin.symm, le_antisymm ?_ ?_⟩
  · intro T hT g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    apply hT
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    rfl
  · intro T hT
    change T ∈ C at hT
    rw [hC] at hT
    rcases hT with ⟨a, rfl⟩
    intro S hS
    change S ∈ C at hS
    rw [hC] at hS
    rcases hS with ⟨b, rfl⟩
    ext c
    exact mul_left_comm b a c

