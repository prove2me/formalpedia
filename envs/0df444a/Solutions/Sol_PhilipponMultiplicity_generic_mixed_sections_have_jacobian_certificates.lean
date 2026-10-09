-- Prove2me | solution 1 for PhilipponMultiplicity.generic_mixed_sections_have_jacobian_certificates
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T21:58:39.893915+00:00
-- url     : https://prove2.me/submissions/5313d248-5f63-4f91-b4bb-ed0b2dfb89c9

import Theorems.Thm_PhilipponMultiplicity_generic_mixed_sections_finite_reduced
import Definitions.Def_PhilipponMultiplicity_GenericMixedSections
import Definitions.Def_PhilipponMultiplicity_GeometricSupport


section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section
namespace PhilipponMultiplicity.GenericMixedSections

/-- Coefficient specialization commutes with a full square Jacobian determinant. -/
theorem map_jacobian_det
    {R S σ : Type*} [CommRing R] [CommRing S] [Fintype σ] [DecidableEq σ]
    (φ : R →+* S) (Q : σ → MvPolynomial σ R) :
    map φ (Matrix.of (fun i j => pderiv j (Q i))).det =
      (Matrix.of (fun i j => pderiv j (map φ (Q i)))).det := by
  rw [show map φ (Matrix.of (fun i j => pderiv j (Q i))).det =
    (Matrix.of (fun i j => map φ (pderiv j (Q i)))).det from
      RingHom.map_det (map φ) _]
  simp only [pderiv_map]

/-- The Jacobian obstruction ideal specializes into the obstruction ideal of
any containing specialized system of equations. -/
theorem map_jacobianIdeal_le
    {R S σ : Type*} [CommRing R] [CommRing S] [Fintype σ] [DecidableEq σ]
    (φ : R →+* S) (I : Ideal (MvPolynomial σ R)) (J : Ideal (MvPolynomial σ S))
    (hIJ : I.map (map φ) ≤ J) :
    (jacobianIdeal I).map (map φ) ≤ jacobianIdeal J := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply sup_le
  · exact Ideal.map_le_iff_le_comap.mp (hIJ.trans le_sup_left)
  · apply Ideal.span_le.mpr
    rintro d ⟨Q, hQ, rfl⟩
    change map φ (Matrix.of (fun i j => pderiv j (Q i))).det ∈ jacobianIdeal J
    rw [map_jacobian_det]
    apply (le_sup_right : _ ≤ jacobianIdeal J)
    apply Ideal.subset_span
    exact ⟨fun i => map φ (Q i), fun i =>
      hIJ (Ideal.mem_map_of_mem (map φ) (hQ i)), rfl⟩


end PhilipponMultiplicity.GenericMixedSections
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.GenericMixedSections

/-- An integral element of a reduced algebra over a perfect field has a
separable minimal polynomial; the algebra need not be a domain. -/
theorem minpoly_separable_of_reduced
    {K A : Type*} [Field K] [PerfectField K] [CommRing A] [Algebra K A]
    [IsReduced A] (x : A) (hx : IsIntegral K x) :
    (minpoly K x).Separable := by
  apply PerfectField.separable_iff_squarefree.mpr
  exact (isRadical_iff_squarefree_of_ne_zero (minpoly.ne_zero hx)).mp
    (minpoly.isRadical K x)

/-- Substituting a coordinate into a univariate polynomial gives a diagonal
Jacobian row. -/
theorem pderiv_polynomial_aeval_X
    {R σ : Type*} [CommRing R] [DecidableEq σ]
    (p : Polynomial R) (i j : σ) :
    pderiv j (Polynomial.aeval (X i : MvPolynomial σ R) p) =
      if i = j then Polynomial.aeval (X i) p.derivative else 0 := by
  rw [(pderiv j).map_aeval]
  by_cases h : i = j <;> simp [pderiv_X, h, smul_eq_mul]

/-- Separability makes the derivative invertible at any root, even in an
arbitrary commutative algebra rather than a field. -/
theorem isUnit_aeval_derivative_of_separable
    {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (p : Polynomial K) (hp : p.Separable) (x : A)
    (hx : Polynomial.aeval x p = 0) :
    IsUnit (Polynomial.aeval x p.derivative) := by
  have h := IsCoprime.map hp (Polynomial.aeval x).toRingHom
  change IsCoprime (Polynomial.aeval x p) (Polynomial.aeval x p.derivative) at h
  rwa [hx, isCoprime_zero_left] at h

/-- A finite reduced quotient over a perfect field has a unit Jacobian
obstruction ideal. Coordinate minimal polynomials give a diagonal Jacobian
whose determinant is already a unit modulo the original ideal. -/
theorem jacobianIdeal_eq_top_of_finite_reduced
    {K σ : Type*} [Field K] [PerfectField K] [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)]
    [IsReduced (MvPolynomial σ K ⧸ I)] :
    jacobianIdeal I = ⊤ := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  let p : σ → Polynomial K := fun i => minpoly K (q (X i))
  let Q : σ → MvPolynomial σ K := fun i => Polynomial.aeval (X i) (p i)
  have hp (i : σ) : (p i).Separable :=
    minpoly_separable_of_reduced _ (IsIntegral.of_finite K _)
  have hQ (i : σ) : Q i ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q (Polynomial.aeval (X i) (p i)) = 0
    rw [← Polynomial.aeval_algHom_apply, minpoly.aeval]
  let d := (Matrix.of (fun i j => pderiv j (Q i))).det
  have hd : d ∈ jacobianIdeal I :=
    (le_sup_right : _ ≤ jacobianIdeal I) (Ideal.subset_span ⟨Q, hQ, rfl⟩)
  have hd_eq : d = ∏ i, Polynomial.aeval (X i) (p i).derivative := by
    change (Matrix.of (fun i j => pderiv j
      (Polynomial.aeval (X i) (p i)))).det = _
    simp only [pderiv_polynomial_aeval_X]
    exact Matrix.det_diagonal
  have hunit : IsUnit (q d) := by
    rw [hd_eq, map_prod]
    apply IsUnit.prod_iff.mpr
    intro i _
    rw [← Polynomial.aeval_algHom_apply]
    exact isUnit_aeval_derivative_of_separable (p i) (hp i) _ (minpoly.aeval K _)
  have ht : (jacobianIdeal I).map q.toRingHom = ⊤ :=
    ((jacobianIdeal I).map q.toRingHom).eq_top_of_isUnit_mem
      (Ideal.mem_map_of_mem _ hd) hunit
  have hc := Ideal.comap_map_of_surjective' q.toRingHom
    Ideal.Quotient.mk_surjective (jacobianIdeal I)
  rw [ht, Ideal.comap_top] at hc
  have hk : RingHom.ker q.toRingHom = I := Ideal.mk_ker
  rw [hk, sup_eq_left.mpr (show I ≤ jacobianIdeal I from le_sup_left)] at hc
  exact hc.symm

end PhilipponMultiplicity.GenericMixedSections
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.GenericMixedSections

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- An equation in the coefficient fraction-field extension of an ideal can
be cleared to a member of the original ideal using a scalar denominator. -/
theorem equation_clear_coefficient_denominator
    {R σ : Type*} [CommRing R] [IsDomain R]
    (I : Ideal (MvPolynomial σ R))
    (q : MvPolynomial σ (FractionRing R))
    (hq : q ∈ I.map (map (algebraMap R (FractionRing R)))) :
    ∃ P : MvPolynomial σ R, P ∈ I ∧ ∃ s : R, s ≠ 0 ∧
      C (algebraMap R (FractionRing R) s) * q =
        map (algebraMap R (FractionRing R)) P := by
  let S := (nonZeroDivisors R).map (C (σ := σ))
  obtain ⟨⟨⟨P, hP⟩, ⟨s, hs⟩⟩, h⟩ :=
    (IsLocalization.mem_map_algebraMap_iff S
      (MvPolynomial σ (FractionRing R))).mp hq
  obtain ⟨s, hs, rfl⟩ := hs
  refine ⟨P, hP, s, mem_nonZeroDivisors_iff_ne_zero.mp hs, ?_⟩
  change q * map (algebraMap R (FractionRing R)) (C s) =
    map (algebraMap R (FractionRing R)) P at h
  simpa only [map_C, mul_comm] using h

/-- Full Jacobian obstruction ideals commute with coefficient localization.
Denominators are constants for all the ambient partial derivatives. -/
theorem map_jacobianIdeal_fraction
    {R σ : Type*} [CommRing R] [IsDomain R] [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ R)) :
    (jacobianIdeal I).map (map (algebraMap R (FractionRing R))) =
      jacobianIdeal (I.map (map (algebraMap R (FractionRing R)))) := by
  classical
  let φ := algebraMap R (FractionRing R)
  let J := (jacobianIdeal I).map (map φ)
  apply le_antisymm
  · exact map_jacobianIdeal_le φ I _ le_rfl
  · apply sup_le
    · exact Ideal.map_mono (show I ≤ jacobianIdeal I from le_sup_left)
    · apply Ideal.span_le.mpr
      rintro d ⟨Q, hQ, rfl⟩
      choose P hP s hs hclear using fun i =>
        equation_clear_coefficient_denominator I (Q i) (hQ i)
      have hderiv (i j : σ) :
          map φ (pderiv j (P i)) = C (φ (s i)) * pderiv j (Q i) := by
        rw [← pderiv_map, ← hclear i, pderiv_C_mul]
      have hdet : map φ (Matrix.of (fun i j => pderiv j (P i))).det =
          (∏ i, C (φ (s i))) * (Matrix.of (fun i j => pderiv j (Q i))).det := by
        rw [show map φ (Matrix.of (fun i j => pderiv j (P i))).det =
          (Matrix.of (fun i j => map φ (pderiv j (P i)))).det from
            RingHom.map_det (map φ) _]
        simp only [hderiv]
        exact Matrix.det_mul_column _ _
      have hmem : map φ (Matrix.of (fun i j => pderiv j (P i))).det ∈ J := by
        apply Ideal.mem_map_of_mem
        exact (le_sup_right : _ ≤ jacobianIdeal I)
          (Ideal.subset_span ⟨P, hP, rfl⟩)
      have hu : IsUnit (∏ i, (C (φ (s i)) : MvPolynomial σ (FractionRing R))) := by
        apply IsUnit.prod_iff.mpr
        intro i _
        apply IsUnit.map C
        apply isUnit_iff_ne_zero.mpr
        exact fun h => hs i ((IsFractionRing.injective R (FractionRing R))
          (h.trans (map_zero φ).symm))
      rw [hdet] at hmem
      exact (J.unit_mul_mem_iff_mem hu).mp hmem

end PhilipponMultiplicity.GenericMixedSections
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport
namespace GenericMixedSections

/-- Finite reduced generic normalized charts provide the original universal
Jacobian certificates. The geometric input is explicit. -/
theorem generic_certificates_of_finite_reduced
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
          Module.Finite (FractionRing (GenericMixedSections.CoeffRing M l))
            (MvPolynomial M.Variable (FractionRing (GenericMixedSections.CoeffRing M l)) ⧸
              (GenericMixedSections.normalizedIdeal M l W b).map
                (GenericMixedSections.genericMap M l)) ∧
          IsReduced (MvPolynomial M.Variable (FractionRing (GenericMixedSections.CoeffRing M l)) ⧸
              (GenericMixedSections.normalizedIdeal M l W b).map
                (GenericMixedSections.genericMap M l)) ∧
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
          (GenericMixedSections.jacobianIdeal
            (GenericMixedSections.normalizedIdeal M l W b)).map
              (GenericMixedSections.genericMap M l) = ⊤ ∧
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by
  have hchar : CharZero K := by
    rcases hK with ⟨e, _⟩ | ⟨p, hp, h⟩
    · exact e.toRingHom.charZero
    · let : Fact p.Prime := ⟨hp⟩
      obtain ⟨e, _⟩ := h
      exact e.toRingHom.charZero
  let : CharZero K := hchar
  intro M W hW hWirr α hα hdim B hB hBW hnonempty l hl b
  obtain ⟨hfinite, hreduced, hboundary⟩ :=
    hgeometry M W hW hWirr α hα hdim B hB hBW hnonempty l hl b
  simp only [genericMap] at hfinite hreduced
  let := hfinite
  let := hreduced
  refine ⟨?_, hboundary⟩
  rw [show genericMap M l = MvPolynomial.map
    (algebraMap (CoeffRing M l) (FractionRing (CoeffRing M l))) from rfl,
    map_jacobianIdeal_fraction]
  exact jacobianIdeal_eq_top_of_finite_reduced _

end GenericMixedSections
end PhilipponMultiplicity
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
          (GenericMixedSections.jacobianIdeal
            (GenericMixedSections.normalizedIdeal M l W b)).map
              (GenericMixedSections.genericMap M l) = ⊤ ∧
          (GenericMixedSections.normalizedIdeal M l B b).map
            (GenericMixedSections.genericMap M l) = ⊤ := by
  exact GenericMixedSections.generic_certificates_of_finite_reduced K hK
    (generic_mixed_sections_finite_reduced K hK)
