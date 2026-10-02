-- Prove2me | solution 1 for PhilipponMultiplicity.exists_filter_regular_mixed_section
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T14:34:59.408177+00:00
-- url     : https://prove2.me/submissions/4b070039-43c0-4fd0-a6fc-284193fb0b19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_reduced_mixed_section_with_primary_avoidance
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertPolynomial_zero_iff_trivial
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_primaryDecomposition
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i


end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_total {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : P.IsHomogeneous (∑ i, D i) := by
  intro a ha
  change (Finsupp.weight (fun _ : M.Variable => (1 : ℕ))) a = _
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => hP a (mem_support_iff.mpr ha) i)

instance degreePiece_finite (D : M.FactorIndex → ℕ) :
    Module.Finite K (Hilbert.degreePiece K M.factorCount M.ambientDimension D) := by
  let W := MvPolynomial.homogeneousSubmodule M.Variable K (∑ i, D i)
  letI : Module.Finite K W := Module.Finite.of_fg
    (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  have hle : Hilbert.degreePiece K M.factorCount M.ambientDimension D ≤ W := by
    intro P hP
    exact M.homogeneous_total ((M.degreePiece_iff P D).mp hP)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)


end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
instance quotientPiece_finite_colon (I : Ideal M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    Module.Finite K (quotientPiece K M.factorCount M.ambientDimension I d) := by
  unfold quotientPiece
  infer_instance
end PhilipponMultiplicity.Hilbert
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_sup_span (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I ⊔ Ideal.span {P}) := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI f hf d
  have hPg : (Ideal.span {P}).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro f hf
    have heq : f = P := Set.mem_singleton_iff.mp hf
    subst f
    exact ⟨D, (M.degreePiece_iff P D).mpr hP⟩
  intro f hf d
  exact weightedHomogeneousComponent_mem_of_mem K w (hIg.sup hPg) hf d


end PhilipponMultiplicity.Hilbert
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [M.blockWeight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d


end PhilipponMultiplicity
end
end

section
namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem homogeneous_cut_chain (l : List M.FactorIndex)
    (J : ℕ → Ideal M.CoordinateRing) (P : ℕ → M.CoordinateRing)
    (hzero : IsMultihomogeneousIdeal M (J 0))
    (hstep : ∀ k (hk : k < l.length),
      M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧ J (k+1) = J k ⊔ Ideal.span {P k}) :
    ∀ k ≤ l.length, IsMultihomogeneousIdeal M (J k) := by
  intro k
  induction k with
  | zero => exact fun _ => hzero
  | succ k ih =>
    intro hk
    obtain ⟨hP,hJ⟩ := hstep k (by omega)
    rw [hJ]
    exact homogeneous_sup_span M _ (ih (by omega)) _ _ hP


end PhilipponMultiplicity.Hilbert
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A zero homogeneous quotient piece means that every polynomial in that
degree already belongs to the ideal. -/
theorem homogeneous_mem_of_hilbertFunction_zero
    (I : Ideal M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hzero : hilbertFunction K M.factorCount M.ambientDimension I D = 0)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D) : P ∈ I := by
  have hbot : quotientPiece K M.factorCount M.ambientDimension I D = ⊥ :=
    Submodule.finrank_eq_zero.mp hzero
  have hmem : Ideal.Quotient.mk I P ∈
      quotientPiece K M.factorCount M.ambientDimension I D :=
    ⟨P, (M.degreePiece_iff P D).mpr hP, rfl⟩
  rw [hbot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hmem)

/-- Irrelevant homogeneous ideals contain every sufficiently large
homogeneous piece, with a bound uniform over all polynomials in that piece. -/
theorem irrelevant_eventually_contains_homogeneous
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hirr : ¬ IsRelevant K M.factorCount M.ambientDimension I.radical) :
    ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
      ∀ P, M.IsHomogeneous P D → P ∈ I := by
  have hz : hilbertPolynomial K M.factorCount M.ambientDimension I = 0 :=
    (hilbertPolynomial_zero_iff_trivial M I hI).mpr hirr
  have hspec := hilbertPolynomial_spec K M.factorCount M.ambientDimension I
    (multigraded_hilbert_polynomial_exists K M I hI)
  rw [hz] at hspec
  obtain ⟨E, hE⟩ := hspec
  refine ⟨E, fun D hD P hP => ?_⟩
  have hzero : hilbertFunction K M.factorCount M.ambientDimension I D = 0 := by
    have h := hE D hD
    simp only [map_zero] at h
    exact_mod_cast h.symm
  exact homogeneous_mem_of_hilbertFunction_zero M I D hzero P hP

/-- A finite primary decomposition has one uniform bound beyond which its
irrelevant components impose no condition. Relevant embedded components
are retained, just like relevant isolated components. -/
theorem PrimaryDecomposition.eventual_relevant_membership
    {I : Ideal M.CoordinateRing} (A : PrimaryDecomposition M I) :
    ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
      ∀ P, M.IsHomogeneous P D →
        (P ∈ I ↔ ∀ j : Fin A.count,
          IsRelevant K M.factorCount M.ambientDimension (A.component j).radical →
          P ∈ A.component j) := by
  classical
  have hchoose (j : Fin A.count) : ∃ E : M.FactorIndex → ℕ,
      ¬ IsRelevant K M.factorCount M.ambientDimension (A.component j).radical →
      ∀ D, (∀ i, E i ≤ D i) → ∀ P, M.IsHomogeneous P D → P ∈ A.component j := by
    by_cases hj : IsRelevant K M.factorCount M.ambientDimension (A.component j).radical
    · exact ⟨0, fun h => (h hj).elim⟩
    · obtain ⟨E, hE⟩ := irrelevant_eventually_contains_homogeneous M
        (A.component j) (A.homogeneous j) hj
      exact ⟨E, fun _ => hE⟩
  choose E hE using hchoose
  refine ⟨fun i => ∑ j, E j i, ?_⟩
  intro D hD P hP
  have hmem : P ∈ I ↔ ∀ j : Fin A.count, P ∈ A.component j := by
    constructor
    · exact fun h j => (A.intersection_eq.le.trans (iInf_le _ j)) h
    · exact fun h => A.intersection_eq.ge (Ideal.mem_iInf.mpr h)
  rw [hmem]
  constructor
  · exact fun h j _ => h j
  · intro h j
    by_cases hj : IsRelevant K M.factorCount M.ambientDimension (A.component j).radical
    · exact h j hj
    · exact hE j hj D (fun i =>
        (Finset.single_le_sum (fun k _ => Nat.zero_le (E k i))
          (Finset.mem_univ j)).trans (hD i)) P hP

/-- Avoiding every relevant primary radical gives filter regularity. No
avoidance is imposed on irrelevant components, and the polynomial need
not itself be homogeneous for this implication. -/
theorem eventual_injective_of_primary_avoidance
    {I : Ideal M.CoordinateRing} (A : PrimaryDecomposition M I)
    (P : M.CoordinateRing)
    (havoid : ∀ j : Fin A.count,
      IsRelevant K M.factorCount M.ambientDimension (A.component j).radical →
      P ∉ (A.component j).radical) :
    ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
      ∀ Q, M.IsHomogeneous Q D → P * Q ∈ I → Q ∈ I := by
  obtain ⟨E, hE⟩ := PrimaryDecomposition.eventual_relevant_membership M A
  refine ⟨E, fun D hD Q hQ hPQ => (hE D hD Q hQ).mpr ?_⟩
  intro j hj
  have hprod : Q * P ∈ A.component j := by
    rw [A.intersection_eq] at hPQ
    simpa only [mul_comm] using (Ideal.mem_iInf.mp hPQ j)
  exact ((Ideal.isPrimary_iff.mp (A.primary j)).2 hprod).resolve_right (havoid j hj)

/-- For a homogeneous ideal, membership in sufficiently large degrees is
detected by localization at the actual relevant primes. The relevant
primary components suffice; irrelevant components have already vanished. -/
theorem eventual_membership_iff_relevant_localizations
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
      ∀ P, M.IsHomogeneous P D →
        (P ∈ I ↔ ∀ q : PrimeSpectrum M.CoordinateRing,
          IsRelevant K M.factorCount M.ambientDimension q.asIdeal →
          algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal) P ∈
            I.map (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal))) := by
  obtain ⟨A⟩ := exists_primaryDecomposition M I hI
  obtain ⟨E, hE⟩ := PrimaryDecomposition.eventual_relevant_membership M A
  refine ⟨E, fun D hD P hP => ?_⟩
  constructor
  · exact fun h q _ => Ideal.mem_map_of_mem _ h
  · intro h
    apply (hE D hD P hP).mpr
    intro j hj
    let q : PrimeSpectrum M.CoordinateRing :=
      ⟨(A.component j).radical, Ideal.isPrime_radical (A.primary j)⟩
    let : q.asIdeal.IsPrime := q.isPrime
    have hle : I ≤ A.component j := A.intersection_eq.le.trans (iInf_le _ j)
    have hmap := (Ideal.map_mono hle) (h q hj)
    have heq := IsLocalization.under_map_of_isPrimary_disjoint
      q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) (A.primary j)
      (Set.disjoint_left.mpr fun x hx hxI => hx (Ideal.le_radical hxI))
    change P ∈ (Ideal.map (algebraMap M.CoordinateRing
      (Localization.AtPrime q.asIdeal)) (A.component j)).under M.CoordinateRing at hmap
    rwa [heq] at hmap

/-- Equality of the localized ideals at all relevant primes implies
equality of their homogeneous pieces in every sufficiently large degree. -/
theorem eventual_homogeneous_mem_iff_of_relevant_localizations_eq
    (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J)
    (hlocal : ∀ q : PrimeSpectrum M.CoordinateRing,
      IsRelevant K M.factorCount M.ambientDimension q.asIdeal →
      I.map (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal)) =
        J.map (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal))) :
    ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
      ∀ P, M.IsHomogeneous P D → (P ∈ I ↔ P ∈ J) := by
  obtain ⟨a, ha⟩ := eventual_membership_iff_relevant_localizations M I hI
  obtain ⟨b, hb⟩ := eventual_membership_iff_relevant_localizations M J hJ
  refine ⟨fun i => max (a i) (b i), fun D hD P hP => ?_⟩
  rw [ha D (fun i => (le_max_left _ _).trans (hD i)) P hP,
    hb D (fun i => (le_max_right _ _).trans (hD i)) P hP]
  constructor <;> intro h q hq
  · rw [← hlocal q hq]; exact h q hq
  · rw [hlocal q hq]; exact h q hq

end PhilipponMultiplicity.Hilbert
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

/-- The geometric input is expressed by finite primary-prime avoidance and
equality of actual localized ideals. Both eventual homogeneous assertions
in the target are proved by the commutative-algebra argument. -/
theorem filter_regular_section_of_primary_local_choice
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hchoice : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∃ A : PrimaryDecomposition M (J k), ∀ j : Fin A.count,
              Hilbert.IsRelevant K M.factorCount M.ambientDimension (A.component j).radical →
              P k ∉ (A.component j).radical) ∧
          (∀ q : PrimeSpectrum M.CoordinateRing,
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.asIdeal →
            (J l.length).map
                (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal)) =
              (M.vanishingIdeal (linearSlice M W L)).map
                (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal)))) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
              ∀ Q, M.IsHomogeneous Q D → P k * Q ∈ J k → Q ∈ J k) ∧
          (∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
            ∀ Q, M.IsHomogeneous Q D →
              (Q ∈ J l.length ↔ Q ∈ M.vanishingIdeal (linearSlice M W L))) := by
  intro M W hW hirr α hα hdim B hB hBW hnonempty
  obtain ⟨L, hL, hfinite, hdisjoint, l, P, J, hcount, hfirst, hstep, hlocal⟩ :=
    hchoice M W hW hirr α hα hdim B hB hBW hnonempty
  have hhom := Hilbert.homogeneous_cut_chain M l J P
    (by rw [hfirst]; exact vanishingIdeal_multihomogeneous K M W)
    (fun k hk => ⟨(hstep k hk).1, (hstep k hk).2.1⟩)
  refine ⟨L, hL, hfinite, hdisjoint, l, P, J, hcount, hfirst, ?_, ?_⟩
  · intro k hk
    obtain ⟨hP, hJ, A, havoid⟩ := hstep k hk
    exact ⟨hP, hJ, Hilbert.eventual_injective_of_primary_avoidance M A (P k) havoid⟩
  · exact Hilbert.eventual_homogeneous_mem_iff_of_relevant_localizations_eq M
      (J l.length) (M.vanishingIdeal (linearSlice M W L)) (hhom l.length le_rfl)
      (vanishingIdeal_multihomogeneous K M _) hlocal

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity PhilipponMultiplicity.SectionThree

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
              ∀ Q, M.IsHomogeneous Q D → P k * Q ∈ J k → Q ∈ J k) ∧
          (∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
            ∀ Q, M.IsHomogeneous Q D →
              (Q ∈ J l.length ↔ Q ∈ M.vanishingIdeal (linearSlice M W L))) := by
  exact filter_regular_section_of_primary_local_choice K hK
    (exists_reduced_mixed_section_with_primary_avoidance K hK)
