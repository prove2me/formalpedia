-- Prove2me | solution 1 for WeierstrassEllipticZeta.quotient_multiplication_rank_nullity
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T00:33:33.257767+00:00
-- url     : https://prove2.me/submissions/57b31a14-7acc-4ed2-871f-ac914f22f858

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section


theorem solution
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (I : Ideal A) (d : ℕ) (β : Module.Basis (Fin d) ℂ (A ⧸ I))
    (ρ : A →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hρ : ∀ p : A, ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p))
    (hlength : ∀ p : A,
      Module.finrank ℂ (A ⧸ I.colon {p}) +
        Module.finrank ℂ (A ⧸ (I ⊔ Ideal.span {p})) = d) :
    ∀ p : A,
      Nonempty ((A ⧸ I.colon {p}) ≃ₗ[ℂ] LinearMap.range (ρ p).mulVecLin) ∧
      (ρ p).rank = Module.finrank ℂ (A ⧸ I.colon {p}) ∧
      Module.finrank ℂ (LinearMap.ker (ρ p).mulVecLin) =
        Module.finrank ℂ (A ⧸ (I ⊔ Ideal.span {p})) ∧
      (ρ p).rank + Module.finrank ℂ (A ⧸ (I ⊔ Ideal.span {p})) = d := by
  classical
  intro p
  let π : A →ₗ[ℂ] (Fin d → ℂ) :=
    β.equivFun.toLinearMap.comp (Ideal.Quotient.mkₐ ℂ I).toLinearMap
  have hsurj : Function.Surjective π :=
    β.equivFun.surjective.comp (Ideal.Quotient.mkₐ_surjective ℂ I)
  let F : A →ₗ[ℂ] (Fin d → ℂ) := (ρ p).mulVecLin.comp π
  have hF (a : A) : F a = β.equivFun (Ideal.Quotient.mk I (p * a)) := by
    change (ρ p).mulVec (β.equivFun (Ideal.Quotient.mk I a)) = _
    simp only [Module.Basis.equivFun_apply, hρ,
      Algebra.leftMulMatrix_mulVec_repr, map_mul]
  have hker : LinearMap.ker F = (I.colon {p}).restrictScalars ℂ := by
    ext a
    change F a = 0 ↔ a ∈ I.colon {p}
    rw [hF, β.equivFun.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
      Submodule.mem_colon_singleton, smul_eq_mul, mul_comm a p]
  have hrange : LinearMap.range F = LinearMap.range (ρ p).mulVecLin :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)
  let E : (A ⧸ I.colon {p}) ≃ₗ[ℂ] LinearMap.range (ρ p).mulVecLin :=
    ((Submodule.quotEquivOfEq ((I.colon {p}).restrictScalars ℂ)
      (LinearMap.ker F) hker.symm).trans F.quotKerEquivRange).trans
        (LinearEquiv.ofEq _ _ hrange)
  have hrank : (ρ p).rank = Module.finrank ℂ (A ⧸ I.colon {p}) :=
    E.finrank_eq.symm
  have hsum : (ρ p).rank + Module.finrank ℂ (A ⧸ (I ⊔ Ideal.span {p})) = d := by
    rw [hrank]
    exact hlength p
  refine ⟨⟨E⟩, hrank, ?_, hsum⟩
  have hnull := (ρ p).mulVecLin.finrank_range_add_finrank_ker
  change (ρ p).rank + Module.finrank ℂ (LinearMap.ker (ρ p).mulVecLin) =
    Module.finrank ℂ (Fin d → ℂ) at hnull
  simp only [Module.finrank_pi, Fintype.card_fin] at hnull
  exact Nat.add_left_cancel (hnull.trans hsum.symm)

