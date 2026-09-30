-- Prove2me | solution 1 for WeierstrassEllipticZeta.multiplication_quotient_range_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T20:07:28.907692+00:00
-- url     : https://prove2.me/submissions/8e1c2329-f328-4c15-a50e-881839241b40

import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Finrank



theorem solution
    (K B V : Type*) [Field K] [CommRing B] [Algebra K B]
    [AddCommGroup V] [Module K V] (e : B ≃ₗ[K] V)
    (P : Module.End K V) (ε : B) (J : Ideal B)
    (hJ : ∀ a, a ∈ J ↔ ε * a = 0)
    (hP : ∀ a, P (e a) = e (ε * a)) :
    ∃ ψ : (B ⧸ J) ≃ₗ[K] LinearMap.range P,
      (∀ a, (ψ (Ideal.Quotient.mk J a) : V) = e (ε * a)) ∧
      Module.finrank K (B ⧸ J) = Module.finrank K (LinearMap.range P) := by
  let f : B →ₗ[K] V := P.comp e.toLinearMap
  have hker : J.restrictScalars K = LinearMap.ker f := by
    ext a
    change a ∈ J ↔ P (e a) = 0
    rw [hP a]
    exact (hJ a).trans ⟨fun h => by rw [h, map_zero],
      fun h => e.injective (h.trans (map_zero e).symm)⟩
  have hrange : LinearMap.range f = LinearMap.range P :=
    LinearMap.range_comp_of_range_eq_top P
      (LinearMap.range_eq_top.mpr e.surjective)
  let ψ : (B ⧸ J) ≃ₗ[K] LinearMap.range P :=
    (Submodule.Quotient.restrictScalarsEquiv K J).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
        f.quotKerEquivRange ≪≫ₗ LinearEquiv.ofEq _ _ hrange
  refine ⟨ψ, ?_, ψ.finrank_eq⟩
  intro a
  change (ψ (Submodule.Quotient.mk a) : V) = e (ε * a)
  simpa only [ψ, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk,
    f, LinearMap.comp_apply, LinearEquiv.coe_coe] using hP a

