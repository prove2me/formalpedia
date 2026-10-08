-- Prove2me | solution 1 for PhilipponMultiplicity.exists_open_preserving_finite_polynomial_mixed_slices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T16:28:43.018731+00:00
-- url     : https://prove2.me/submissions/090e405b-a3a7-4703-8e48-78ebe810d5f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_quasifinite_mixed_slices
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
import Mathlib


section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity.SpecializationFiber
open MvPolynomial

def specialize {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) : MvPolynomial δ R →ₐ[K] R :=
  (MvPolynomial.aeval (fun i => algebraMap K R (c i))).restrictScalars K

@[simp] theorem specialize_C {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) (r : R) : specialize c (C r) = r := by
  simp [specialize]

@[simp] theorem specialize_X {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) (i : δ) : specialize (R := R) c (X i) = algebraMap K R (c i) := by
  simp [specialize]

theorem specialize_surjective {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) : Function.Surjective (specialize (R := R) c) :=
  fun r => ⟨C r, specialize_C c r⟩

theorem specialize_comp {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) :
    (specialize (R := R) c).toRingHom.comp
      (algebraMap (MvPolynomial δ K) (MvPolynomial δ R)) =
        (algebraMap K R).comp (MvPolynomial.eval c) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    change specialize c (MvPolynomial.map (algebraMap K R) (C k)) =
      algebraMap K R (MvPolynomial.eval c (C k))
    rw [MvPolynomial.map_C, specialize_C, MvPolynomial.eval_C]
  · intro i
    change specialize c (MvPolynomial.map (algebraMap K R) (X i)) =
      algebraMap K R (MvPolynomial.eval c (X i))
    rw [MvPolynomial.map_X, specialize_X, MvPolynomial.eval_X]

/-- Specializing coefficient variables has exactly the extended evaluation
ideal as kernel, over an arbitrary coefficient algebra. -/
theorem ker_specialize {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) :
    RingHom.ker (specialize (R := R) c) =
      (RingHom.ker (MvPolynomial.eval c)).map
        (algebraMap (MvPolynomial δ K) (MvPolynomial δ R)) := by
  let L := (RingHom.ker (MvPolynomial.eval c)).map
    (algebraMap (MvPolynomial δ K) (MvPolynomial δ R))
  have hrel (i : δ) : C (algebraMap K R (c i)) - X i ∈ L := by
    have h : C (c i) - X i ∈ RingHom.ker (MvPolynomial.eval c) := by
      simp [RingHom.mem_ker]
    have hm := Ideal.mem_map_of_mem
      (algebraMap (MvPolynomial δ K) (MvPolynomial δ R)) h
    change MvPolynomial.map (algebraMap K R) (C (c i) - X i) ∈ L at hm
    simpa only [map_sub, MvPolynomial.map_C, MvPolynomial.map_X] using hm
  have hdiff (P : MvPolynomial δ R) : C (specialize c P) - P ∈ L := by
    induction P using MvPolynomial.induction_on with
    | C r => simp
    | add P Q hP hQ =>
      simpa only [map_add, add_sub_add_comm] using L.add_mem hP hQ
    | mul_X P i hP =>
      simpa only [map_mul, specialize_X] using L.mul_sub_mul_mem hP (hrel i)
  apply le_antisymm
  · intro P hP
    have hz : specialize c P = 0 := hP
    simpa only [hz, map_zero, zero_sub, neg_mem_iff] using hdiff P
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    change specialize c ((algebraMap (MvPolynomial δ K) (MvPolynomial δ R)) P) = 0
    have he := RingHom.congr_fun (specialize_comp (R := R) c) P
    change specialize c ((algebraMap (MvPolynomial δ K) (MvPolynomial δ R)) P) =
      algebraMap K R (MvPolynomial.eval c P) at he
    rw [he]
    rw [show MvPolynomial.eval c P = 0 from hP, map_zero]

/-- The fiber of a quotient under a surjective specialization is the quotient
by the specialized ideal, without replacing either ideal by its radical. -/
def quotientFiberEquiv {K P R : Type*} [CommRing K] [CommRing P] [CommRing R]
    [Algebra K P] [Algebra K R] (f : P →ₐ[K] R) (hf : Function.Surjective f)
    (J : Ideal P) :
    ((P ⧸ J) ⧸ (RingHom.ker f).map (Ideal.Quotient.mk J)) ≃ₐ[K]
      (R ⧸ J.map f) := by
  let g := (Ideal.Quotient.mkₐ K (J.map f)).comp f
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hf
  have hker : RingHom.ker g = J ⊔ RingHom.ker f := by
    change RingHom.ker ((Ideal.Quotient.mk (J.map f)).comp f.toRingHom) = _
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact Ideal.comap_map_of_surjective f.toRingHom hf J
  exact (DoubleQuot.quotQuotEquivQuotSupₐ K J (RingHom.ker f)).trans
    ((Ideal.quotientEquivAlgOfEq K hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hg))

/-- Finite fibers imply quasi-finiteness at every prime over that fiber.
Zariski's main theorem supplies the passage to Mathlib's local-algebra form. -/
theorem quasiFiniteAt_of_finite_fiber
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra.FiniteType A B] (p : Ideal A) (q : Ideal B) [q.IsPrime]
    (hqp : q.under A = p)
    (hfinite : Module.Finite K (B ⧸ p.map (algebraMap A B))) :
    Algebra.QuasiFiniteAt A q := by
  subst p
  letI := hfinite
  haveI : Module.Finite A (B ⧸ (q.under A).map (algebraMap A B)) :=
    Module.Finite.of_restrictScalars_finite K A _
  haveI : Algebra.WeaklyQuasiFiniteAt A q := inferInstance
  exact Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt q

end PhilipponMultiplicity.SpecializationFiber
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open scoped BigOperators
noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity.MixedFamily
open MvPolynomial SpecializationFiber
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem specialize_fixed (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) :
    (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom.comp
      (fixed M l) = Polynomial.C := by
  apply RingHom.ext
  intro P
  change specialize (Function.uncurry c) (MvPolynomial.C (Polynomial.C P)) = Polynomial.C P
  exact specialize_C _ _

theorem specialize_row (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (j : Fin l.length) :
    specialize (R := SlicePolynomial M) (Function.uncurry c) (row M l j) =
      Polynomial.C (MixedFlag.polynomial M l c j) := by
  classical
  simp [row, fixed, MixedFlag.polynomial, MixedFlag.rowForm, Algebra.smul_def,
    MvPolynomial.algebraMap_eq]

/-- Fixing the coefficient parameters recovers exactly the normalized mixed
equations and the inverse equation used in the original finite slice. -/
theorem specialize_ideal (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing) (c : Fin l.length → M.Variable → K) :
    (ideal M W l b H).map (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom =
      (((MixedFlag.ideal M (M.vanishingIdeal W) l c l.length) ⊔
        Ideal.span (Set.range (fun i : M.FactorIndex =>
          (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
          Polynomial.C ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1}) := by
  have hf (I : Ideal M.CoordinateRing) :
      (I.map (fixed M l)).map
        (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom =
          I.map Polynomial.C := by
    rw [Ideal.map_map, specialize_fixed]
  simp only [ideal, Ideal.map_sup, hf]
  have hrow (j : Fin l.length) :
      (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom (row M l j) =
        Polynomial.C (MixedFlag.polynomial M l c j) := specialize_row M l c j
  have hconst (P : SlicePolynomial M) :
      (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom (C P) = P :=
    specialize_C _ _
  simp only [MixedFlag.ideal, Ideal.map_sup, Ideal.map_iSup, Ideal.map_span,
    Set.image_singleton, hrow, hconst]

theorem parameter_ideal_eq_kernel (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) :
    (MvPolynomial.vanishingIdeal K {Function.uncurry c}).map
      (algebraMap (ParameterRing M l) (TotalPolynomial M l)) =
        RingHom.ker (specialize (R := SlicePolynomial M) (Function.uncurry c)) := by
  rw [ker_specialize]
  congr 1
  ext P
  simp [RingHom.mem_ker]

/-- Finiteness of the explicit initial slice is finiteness of the actual
closed fiber of the universal coefficient algebra. -/
theorem finite_fiber (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing) (c : Fin l.length → M.Variable → K)
    (hfinite : Module.Finite K ((Polynomial M.CoordinateRing) ⧸
      (((MixedFlag.ideal M (M.vanishingIdeal W) l c l.length) ⊔
        Ideal.span (Set.range (fun i : M.FactorIndex =>
          (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
          Polynomial.C ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1}))) :
    Module.Finite K ((CoordinateRing M W l b H) ⧸
      (MvPolynomial.vanishingIdeal K {Function.uncurry c}).map
        (algebraMap (ParameterRing M l) (CoordinateRing M W l b H))) := by
  let J := ideal M W l b H
  let f := specialize (R := SlicePolynomial M) (Function.uncurry c)
  haveI : Module.Finite K (SlicePolynomial M ⧸ J.map f) := by
    change Module.Finite K (SlicePolynomial M ⧸ (ideal M W l b H).map
      (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom)
    rw [specialize_ideal]
    exact hfinite
  have hparam : (MvPolynomial.vanishingIdeal K {Function.uncurry c}).map
      (algebraMap (ParameterRing M l) (CoordinateRing M W l b H)) =
        (RingHom.ker f).map (Ideal.Quotient.mk J) := by
    rw [← parameter_ideal_eq_kernel M l c, Ideal.map_map]
    rfl
  rw [hparam]
  exact Module.Finite.equiv
    (quotientFiberEquiv f (specialize_surjective _) J).symm.toLinearEquiv

/-- The universal mixed family is quasi-finite at every prime of a finite
initial slice. This uses the actual family, with all coefficient variables. -/
theorem quasiFiniteAt_fiber (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing) (c : Fin l.length → M.Variable → K)
    (hfinite : Module.Finite K ((Polynomial M.CoordinateRing) ⧸
      (((MixedFlag.ideal M (M.vanishingIdeal W) l c l.length) ⊔
        Ideal.span (Set.range (fun i : M.FactorIndex =>
          (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
          Polynomial.C ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1})))
    (q : PrimeSpectrum (CoordinateRing M W l b H))
    (hq : q.asIdeal.under (ParameterRing M l) =
      MvPolynomial.vanishingIdeal K {Function.uncurry c}) :
    Algebra.QuasiFiniteAt (ParameterRing M l) q.asIdeal := by
  haveI : Algebra.FiniteType (ParameterRing M l) (CoordinateRing M W l b H) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  exact quasiFiniteAt_of_finite_fiber _ q.asIdeal hq (finite_fiber M W l b H c hfinite)

end PhilipponMultiplicity.MixedFamily
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem finite_polynomial_persistence_of_quasifinite_slices
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            ∀ q : PrimeSpectrum (MixedFamily.CoordinateRing M W l b H),
              q.asIdeal.under (MixedFamily.ParameterRing M l) =
                MvPolynomial.vanishingIdeal K {Function.uncurry c₀} →
              Algebra.QuasiFiniteAt (MixedFamily.ParameterRing M l) q.asIdeal) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0})) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            Module.Finite K ((Polynomial M.CoordinateRing) ⧸
              (((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
                Ideal.span (Set.range (fun i : M.FactorIndex =>
                  (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
                  Polynomial.C ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1}))) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  intro M W hW hirr α hα hdim l hl c₀ S hS hSZ hfinite
  apply hgeometry M W hW hirr α hα hdim l hl c₀ S hS hSZ
  intro x hx
  obtain ⟨b,v,hb,hrep,H,a,ha,hQ⟩ := hfinite x hx
  refine ⟨b,v,hb,hrep,H,a,ha,?_⟩
  intro q hq
  exact MixedFamily.quasiFiniteAt_fiber M W l b H c₀ hQ q hq

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            Module.Finite K ((Polynomial M.CoordinateRing) ⧸
              (((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
                Ideal.span (Set.range (fun i : M.FactorIndex =>
                  (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
                  Polynomial.C ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1}))) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  exact finite_polynomial_persistence_of_quasifinite_slices K hK
    (exists_open_preserving_quasifinite_mixed_slices K hK)
