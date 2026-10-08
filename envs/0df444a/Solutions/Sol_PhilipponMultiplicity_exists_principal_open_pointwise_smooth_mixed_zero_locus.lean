-- Prove2me | solution 1 for PhilipponMultiplicity.exists_principal_open_pointwise_smooth_mixed_zero_locus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-05T21:30:33.161383+00:00
-- url     : https://prove2.me/submissions/b135d5c9-a739-4829-84c3-240f3514e876
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_principal_open_mixed_jacobian_presentations
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

set_option autoImplicit false

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM

theorem primeCompl_map_quotient {R : Type*} [CommRing R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
    p.primeCompl.map (Ideal.Quotient.mk I) = (p.map (Ideal.Quotient.mk I)).primeCompl := by
  letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · rintro ⟨s, hs, heq⟩
    change Ideal.Quotient.mk I r ∉ p.map (Ideal.Quotient.mk I)
    rw [← heq, Ideal.mem_quotient_iff_mem hIp]
    exact hs
  · intro h
    refine ⟨r, ?_, rfl⟩
    exact fun hr => h (Ideal.mem_map_of_mem _ hr)

/-- The two actual rings obtained by quotienting and localizing commute.
This is the identification needed between smooth affine rings and the local
quotients in Philippon's definition. -/
def localizedQuotientEquiv {R : Type*} [CommRing R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
    ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≃ₐ[R ⧸ I]
      Localization.AtPrime (p.map (Ideal.Quotient.mk I)) := by
  letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  let B := (Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))
  haveI : IsLocalization (p.map (Ideal.Quotient.mk I)).primeCompl B := by
    rw [← primeCompl_map_quotient I p hIp]
    exact inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl) B)
  exact IsLocalization.algEquiv (p.map (Ideal.Quotient.mk I)).primeCompl B _

end PhilipponMultiplicity.AlgebraicGroupCM

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosedPointSmoothness

/-- Smoothness is unchanged by commuting quotient and localization. The
equivalence respects the ground field, not just the underlying rings. -/
theorem point_local_iff_quotient_local
    {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
    Algebra.FormallySmooth K
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ↔
      Algebra.IsSmoothAt K (p.map (Ideal.Quotient.mk I)) := by
  letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  letI : IsScalarTower K (R ⧸ I)
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.FormallySmooth.iff_of_equiv
    ((AlgebraicGroupCM.localizedQuotientEquiv I p hIp).restrictScalars K)
end ClosedPointSmoothness
end PhilipponMultiplicity
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AffineJacobian.LocalSmoothness
open MvPolynomial

/-- A finite polynomial presentation is smooth wherever its chosen Jacobian
minor is nonzero. This allows arbitrary relative dimension. -/
theorem isSmoothAt_of_jacobian_not_mem
    {B C ι τ : Type*} [CommRing B] [CommRing C] [Algebra B C]
    [Finite ι] [Finite τ] (P : Algebra.PreSubmersivePresentation B C ι τ)
    (q : Ideal C) [q.IsPrime] (hq : P.jacobian ∉ q) : Algebra.IsSmoothAt B q := by
  letI : Algebra.FinitePresentation B C := P.finitePresentation_of_isFinite
  let j := P.jacobian
  let D := Localization.Away j
  let Q := (Algebra.PreSubmersivePresentation.localizationAway D j).comp P
  have hunit : IsUnit Q.jacobian := by
    change IsUnit ((Algebra.PreSubmersivePresentation.localizationAway D j).comp P).jacobian
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def, Algebra.PreSubmersivePresentation.localizationAway_jacobian]
    exact (IsLocalization.Away.algebraMap_isUnit j).mul
      (IsLocalization.Away.algebraMap_isUnit j)
  let Q' : Algebra.SubmersivePresentation B D (Unit ⊕ ι) (Unit ⊕ τ) :=
    { Q with jacobian_isUnit := hunit }
  letI : Algebra.IsStandardSmooth B D := Q'.isStandardSmooth
  have hsub : (PrimeSpectrum.basicOpen j : Set (PrimeSpectrum C)) ⊆
      Algebra.smoothLocus B C :=
    Algebra.basicOpen_subset_smoothLocus_iff.mpr inferInstance
  exact hsub (show (⟨q, inferInstance⟩ : PrimeSpectrum C) ∈ PrimeSpectrum.basicOpen j from hq)

/-- The explicit derivative minor is the Jacobian of the naive quotient
presentation. Its nonvanishing at a point yields smoothness at that point. -/
theorem smooth_quotient_of_minor
    {K σ : Type*} [Field K] [Finite σ]
    (r : ℕ) (F : Fin r → MvPolynomial σ K) (e : Fin r ↪ σ)
    (a : σ → K) (hF : ∀ i, eval a (F i) = 0)
    (hdet : eval a (Matrix.of (fun i j : Fin r => pderiv (e i) (F j))).det ≠ 0) :
    let I := Ideal.span (Set.range F)
    Algebra.FormallySmooth K
      ((Localization.AtPrime (vanishingIdeal K {a})) ⧸
        I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime (vanishingIdeal K {a})))) := by
  classical
  let I := Ideal.span (Set.range F)
  let p := vanishingIdeal K {a}
  have hIp : I ≤ p := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simpa [p,vanishingIdeal] using hF i
  let q := p.map (Ideal.Quotient.mk I)
  letI : q.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  let P : Algebra.PreSubmersivePresentation K ((MvPolynomial σ K) ⧸ I) σ (Fin r) :=
    { Algebra.Presentation.naive (v := F) with map := e, map_inj := e.injective }
  have hmatrix : P.jacobiMatrix = Matrix.of (fun i j : Fin r => pderiv (e i) (F j)) := by
    ext i j
    rw [P.jacobiMatrix_apply]
    rfl
  have hmap : algebraMap P.Ring ((MvPolynomial σ K) ⧸ I) = Ideal.Quotient.mk I := by
    rw [P.algebraMap_eq]
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [RingHom.coe_coe, aeval_C]
      rfl
    · intro i
      simp only [RingHom.coe_coe, aeval_X]
      rfl
  have hq : P.jacobian ∉ q := by
    rw [P.jacobian_eq_jacobiMatrix_det,hmatrix,hmap]
    intro h
    have hp := (Ideal.mem_quotient_iff_mem hIp).mp h
    apply hdet
    simpa [p,vanishingIdeal] using hp
  have hs := isSmoothAt_of_jacobian_not_mem P q hq
  exact (PhilipponMultiplicity.ClosedPointSmoothness.point_local_iff_quotient_local
    (K := K) I p hIp).mpr hs

/-- Equality of the actual localized ideals transfers the Jacobian criterion
to a local generating family, without asserting global ideal generation. -/
theorem smooth_local_quotient_of_generators
    {K σ : Type*} [Field K] [Finite σ]
    (J : Ideal (MvPolynomial σ K)) (a : σ → K)
    (r : ℕ) (F : Fin r → MvPolynomial σ K) (e : Fin r ↪ σ)
    (hF : ∀ i, eval a (F i) = 0)
    (hgen : (Ideal.span (Set.range F)).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime (vanishingIdeal K {a}))) =
      J.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime (vanishingIdeal K {a}))))
    (hdet : eval a (Matrix.of (fun i j : Fin r => pderiv (e i) (F j))).det ≠ 0) :
    Algebra.FormallySmooth K
      ((Localization.AtPrime (vanishingIdeal K {a})) ⧸
        J.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime (vanishingIdeal K {a})))) := by
  have hs := smooth_quotient_of_minor r F e a hF hdet
  exact (Algebra.FormallySmooth.iff_of_equiv
    (Ideal.quotientEquivAlgOfEq K hgen)).mp hs

end AffineJacobian.LocalSmoothness
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem pointwise_smooth_mixed_of_local_jacobian
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                ∃ (r : ℕ) (Q : Fin r → M.CoordinateRing) (e : Fin r ↪ M.Variable),
                  (∀ i, MvPolynomial.eval v (Q i) = 0) ∧
                  (Ideal.span (Set.range Q)).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))) =
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))) ∧
                  MvPolynomial.eval v
                    (Matrix.of (fun i j : Fin r => MvPolynomial.pderiv (e i) (Q j))).det ≠ 0)) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                Algebra.FormallySmooth K
                  ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) := by
  classical
  intro M W hW hWirr α hα hdim B hB hBW hne l hl
  obtain ⟨F,hF,hs⟩ := hgeometry M W hW hWirr α hα hdim B hB hBW hne l hl
  refine ⟨F,hF,?_⟩
  intro c hc
  obtain ⟨hfinite,hdisj,hlocal⟩ := hs c hc
  refine ⟨hfinite,hdisj,?_⟩
  intro v hv hJ
  obtain ⟨r,Q,e,hQ,hgen,hdet⟩ := hlocal v hv hJ
  exact AffineJacobian.LocalSmoothness.smooth_local_quotient_of_generators
    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length) v r Q e hQ hgen hdet

end PhilipponMultiplicity
end

end

set_option maxHeartbeats 1200000
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
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                Algebra.FormallySmooth K
                  ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) := by
  exact pointwise_smooth_mixed_of_local_jacobian K hK
    (exists_principal_open_mixed_jacobian_presentations K hK)
