-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.torus_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:17.921355+00:00
-- url     : https://prove2.me/submissions/e90a30eb-f4d6-4ba6-98cd-913beb7d72ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (A X : Type) [CommRing A] [Nontrivial A] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ X) A (AddMonoidAlgebra A X) := by
  classical
  let b := Module.finBasis ℤ X
  let f : (Fin (Module.finrank ℤ X) →₀ ℕ) →+ X :=
    b.repr.symm.toLinearMap.toAddMonoidHom.comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))
  have hf : Function.Injective f := b.repr.symm.injective.comp (Finsupp.mapRange_injective _ Nat.cast_zero Nat.cast_injective)
  let P := MvPolynomial (Fin (Module.finrank ℤ X)) A
  let φ : P →ₐ[A] AddMonoidAlgebra A X := AddMonoidAlgebra.mapDomainAlgHom A A f
  have hφ : ∀ m a, φ (MvPolynomial.monomial m a) = AddMonoidAlgebra.single (f m) a := fun m a =>
    AddMonoidAlgebra.mapDomain_single
  let _ : Algebra P (AddMonoidAlgebra A X) := φ.toRingHom.toAlgebra
  have : IsScalarTower A P (AddMonoidAlgebra A X) := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let one : Fin (Module.finrank ℤ X) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1
  have hr : ∀ n : ℕ, algebraMap P (AddMonoidAlgebra A X) (MvPolynomial.monomial one 1) ^ n =
      AddMonoidAlgebra.single (n • f one) 1 := fun n => by
    show φ _ ^ n = _
    rw [hφ, AddMonoidAlgebra.single_pow, one_pow]
  have : IsLocalization.Away (MvPolynomial.monomial one (1 : A) : P) (AddMonoidAlgebra A X) := by
    refine IsLocalization.Away.mk _ ?_ (fun s => ?_) (fun a c h => ⟨0, by rw [AddMonoidAlgebra.mapDomain_injective hf h]⟩)
    · refine IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-f one) 1) ?_
      show φ _ * _ = _
      rw [hφ, AddMonoidAlgebra.single_mul_single, add_neg_cancel, _root_.one_mul]; rfl
    · induction s using AddMonoidAlgebra.induction_linear with
      | zero => exact ⟨0, 0, by simp⟩
      | add s t hs ht =>
        obtain ⟨n, a, ha⟩ := hs
        obtain ⟨m, c, hc⟩ := ht
        refine ⟨n + m, a * MvPolynomial.monomial one 1 ^ m + c * MvPolynomial.monomial one 1 ^ n, ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, ← ha, ← hc]; ring
      | single x a =>
        let n : ℕ := ∑ i, (b.repr x i).natAbs
        refine ⟨n, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (b.repr x i + n).toNat) a, ?_⟩
        show _ = φ _
        rw [hr, hφ, AddMonoidAlgebra.single_mul_single, _root_.mul_one]
        congr 1
        apply b.repr.injective
        ext i
        have h₁ : (b.repr x i).natAbs ≤ n := Finset.single_le_sum (f := fun i => (b.repr x i).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        simp [f, one]
        omega
  have : Algebra.IsStandardSmooth A P := Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.2
    ⟨inferInstance, _, KaehlerDifferential.mvPolynomialBasis A _, by rintro _ ⟨i, rfl⟩; exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply A _ i).symm⟩⟩
  have : Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ X) A P :=
    (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).2 (by
      rw [rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis A _), Fintype.card_fin])
  have := Algebra.IsStandardSmoothOfRelativeDimension.localization_away (S := AddMonoidAlgebra A X)
    (MvPolynomial.monomial one (1 : A) : P)
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans (Module.finrank ℤ X) 0 A P (AddMonoidAlgebra A X)
  rwa [zero_add] at h
end ReciprocityTheory.ChartRestriction.G.H1
