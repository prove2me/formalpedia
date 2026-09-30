-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.componentSum_cut_le_on_cutLocus
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T13:17:59.943447+00:00
-- url     : https://prove2.me/submissions/4401450e-77c5-4181-872e-083f6d73abd9

import Definitions.Def_PhilipponMultiplicity_CutLocus
import Mathlib.RingTheory.Lasker
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_meetsOpen_inf_away_iff
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_primaryDecomposition
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_component_partition_cut
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_regular_cut_le_of_equidimensional
import Theorems.Thm_PhilipponMultiplicity_Hilbert_cohenMacaulayAt_associated_isMinimal
import Theorems.Thm_PhilipponMultiplicity_Hilbert_primaryComponent_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_antitone
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_eq_of_radical_eq
import Theorems.Thm_PhilipponMultiplicity_Hilbert_degreeValue_antitone_of_dimension_eq
import Theorems.Thm_PhilipponMultiplicity_Hilbert_component_length_formula
import Theorems.Thm_PhilipponMultiplicity_Hilbert_primaryComponent_degreeValue_eq_localLength
import Theorems.Thm_PhilipponMultiplicity_Hilbert_exists_relevant_minimalPrime_dimension_eq
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_hypersurface_component_dimension
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Pointwise
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport
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

namespace PhilipponMultiplicity.ComponentSelection

theorem finite_iInf_le_prime {R ι : Type*} [CommRing R] [Finite ι]
    (A : ι → Ideal R) (q : Ideal R) (hq : q.IsPrime) :
    (⨅ i, A i) ≤ q ↔ ∃ i, A i ≤ q := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Finset.mem_univ, true_and] using
    (hq.inf_le' (s := Finset.univ) (f := A))

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.ComponentSelection
variable {R : Type*} [CommRing R]

theorem minimalPrime_of_between {J I q : Ideal R}
    (hq : q ∈ J.minimalPrimes) (hJI : J ≤ I) (hIq : I ≤ q) :
    q ∈ I.minimalPrimes :=
  ⟨⟨hq.1.1, hIq⟩, fun r hr hrq => hq.2 ⟨hr.1, hJI.trans hr.2⟩ hrq⟩

theorem le_associatedPrime {I q : Ideal R}
    (hq : q ∈ associatedPrimes R (R ⧸ I)) : I ≤ q := by
  simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using
    hq.annihilator_le

theorem minimalPrime_isAssociated [IsNoetherianRing R] {I q : Ideal R}
    (hq : q ∈ I.minimalPrimes) : q ∈ associatedPrimes R (R ⧸ I) := by
  apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R (R ⧸ I)
  simpa only [Ideal.annihilator_quotient] using hq

theorem radical_eq_of_prime_containment (A B : Ideal R)
    (h : ∀ q : Ideal R, q.IsPrime → (A ≤ q ↔ B ≤ q)) : A.radical = B.radical := by
  rw [Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
  congr 1
  ext q
  exact ⟨fun hq => ⟨(h q hq.2).mp hq.1, hq.2⟩,
    fun hq => ⟨(h q hq.2).mpr hq.1, hq.2⟩⟩

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.ComponentSelection
variable {R : Type*} [CommRing R]

theorem associatedPrimes_quotient_eq (I : Ideal R) :
    associatedPrimes R (R ⧸ I) = I.associatedPrimes := by
  have hc (f : R) : (⊥ : Submodule R (R ⧸ I)).colon {Ideal.Quotient.mk I f} = I.colon {f} := by
    ext x
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
    rfl
  ext q
  constructor
  · rintro ⟨hp, x, heq⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨hp, f, heq.trans (congrArg Ideal.radical (hc f))⟩
  · rintro ⟨hp, f, heq⟩
    exact ⟨hp, Ideal.Quotient.mk I f, heq.trans (congrArg Ideal.radical (hc f).symm)⟩

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.SectionThreeSupport
open ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The supplied genuine minimal primary decomposition has exactly the
actual associated primes of the quotient, including embedded primes. -/
theorem PrimaryDecomposition.associatedPrimes_eq (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) :
    associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) =
      Set.range (fun i => (D.component i).radical) := by
  classical
  let S : Finset (Ideal M.CoordinateRing) := Finset.univ.image D.component
  have hS : Submodule.IsMinimalPrimaryDecomposition I S := by
    constructor
    · simpa only [S, Finset.inf_image, Finset.inf_univ_eq_iInf, Function.comp_id,
        Function.comp_def, id_eq] using D.intersection_eq.symm
    · intro Q hQ
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
      exact D.primary i
    · intro Q hQ T hT hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hT
      simp only [Function.onFun, Submodule.colon_univ]
      exact fun h => hne (congrArg D.component (D.radicals_injective h))
    · intro Q hQ hle
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
      let A : Ideal M.CoordinateRing := ⨅ j : {j : Fin D.count // j ≠ i}, D.component j.1
      have hdrop : A ≤ (S.erase (D.component i)).inf id := by
        apply Finset.le_inf_iff.mpr
        intro Q hQ
        obtain ⟨hneq, hmem⟩ := Finset.mem_erase.mp hQ
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hmem
        have hji : j ≠ i := fun h => hneq (congrArg D.component h)
        exact iInf_le _ (⟨j, hji⟩ : {j : Fin D.count // j ≠ i})
      have hAI : A ≤ I := by
        apply le_trans (b := ⨅ j, D.component j) _ D.intersection_eq.symm.le
        apply le_iInf
        intro j
        by_cases hji : j = i
        · exact hji ▸ hdrop.trans hle
        · exact iInf_le _ (⟨j, hji⟩ : {j : Fin D.count // j ≠ i})
      have hIA : I ≤ A := by
        apply le_iInf
        intro j
        exact D.intersection_eq.le.trans (iInf_le _ j.1)
      exact D.irredundant i (le_antisymm hAI hIA)
  rw [associatedPrimes_quotient_eq, ← hS.image_radical_eq_associated_primes]
  ext q
  simp only [Set.mem_image, Finset.mem_coe, S, Finset.mem_image,
    Finset.mem_univ, true_and, Submodule.colon_univ, Set.mem_range]
  constructor
  · rintro ⟨Q, ⟨i, rfl⟩, heq⟩
    exact ⟨i, heq⟩
  · rintro ⟨i, rfl⟩
    exact ⟨D.component i, ⟨i, rfl⟩, rfl⟩

end PhilipponMultiplicity.SectionThreeSupport

namespace PhilipponMultiplicity.PrimaryComponentSupport

private theorem primary_localization_map_iInf {R ι : Type*} [CommRing R] [Finite ι]
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    (Q : ι → Ideal R) :
    (⨅ i, Q i).map (algebraMap R A) = ⨅ i, (Q i).map (algebraMap R A) := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Function.comp_def, IsLocalization.mapFrameHom_apply]
    using map_finset_inf (IsLocalization.mapFrameHom S A) Finset.univ Q

open SectionThree SectionThreeSupport ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The canonical contraction from a minimal-prime localization equals the
corresponding member of any minimal primary decomposition. -/
theorem primaryComponent_eq_decomposition (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    ∃ i : Fin D.count, (D.component i).radical = q.asIdeal ∧
      Hilbert.primaryComponent K M.factorCount M.ambientDimension I q = D.component i := by
  classical
  obtain ⟨i, hi⟩ := (finite_iInf_le_prime D.component q.asIdeal q.isPrime).mp
    (D.intersection_eq.symm.le.trans hq.1.2)
  have hrad (j : Fin D.count) (hj : D.component j ≤ q.asIdeal) :
      (D.component j).radical = q.asIdeal := by
    have hle := q.isPrime.radical_le_iff.mpr hj
    have hI : I ≤ (D.component j).radical :=
      (D.intersection_eq.le.trans (iInf_le D.component j)).trans Ideal.le_radical
    exact le_antisymm hle (hq.2 ⟨Ideal.isPrime_radical (D.primary j), hI⟩ hle)
  have hri := hrad i hi
  let A := Localization.AtPrime q.asIdeal
  let f := algebraMap M.CoordinateRing A
  have hmap : I.map f = (D.component i).map f := by
    apply (congrArg (Ideal.map f) D.intersection_eq).trans
    rw [primary_localization_map_iInf q.asIdeal.primeCompl A]
    apply le_antisymm (iInf_le _ i)
    refine le_iInf fun j => ?_
    by_cases heq : j = i
    · subst j; exact le_rfl
    · have hnot : ¬ D.component j ≤ q.asIdeal := by
        intro hj
        exact heq (D.radicals_injective ((hrad j hj).trans hri.symm))
      rw [IsLocalization.AtPrime.map_eq_top_of_not_le (S := A) hnot]
      exact le_top
  refine ⟨i, hri, ?_⟩
  change (I.map f).comap f = D.component i
  rw [hmap]
  exact IsLocalization.under_map_of_isPrimary_disjoint q.asIdeal.primeCompl A (D.primary i)
    (Set.disjoint_left.mpr fun x hx hxI => hx (hi hxI))

end PhilipponMultiplicity.PrimaryComponentSupport

namespace PhilipponMultiplicity.RegularCutSupport
variable {R : Type*} [CommRing R]

/-- Localization commutes with a finite intersection of ideals. -/
theorem localization_map_iInf {ι : Type*} [Finite ι]
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    (Q : ι → Ideal R) :
    (⨅ i, Q i).map (algebraMap R A) = ⨅ i, (Q i).map (algebraMap R A) := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Function.comp_def, IsLocalization.mapFrameHom_apply]
    using map_finset_inf (IsLocalization.mapFrameHom S A) Finset.univ Q


end PhilipponMultiplicity.RegularCutSupport

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree ComponentSelection PrimaryComponentSupport RegularCutSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem retainedPart_le_prime_iff (J I q : Ideal M.CoordinateRing) (hq : q.IsPrime) :
    retainedPart M J I ≤ q ↔
      ∃ p ∈ J.minimalPrimes,
        p ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) ∧ p ≤ q := by
  classical
  unfold retainedPart
  rw [finite_iInf_le_prime _ q hq]
  constructor
  · rintro ⟨p, hp⟩
    split_ifs at hp with ha
    · refine ⟨p.1.asIdeal, p.2, ha, ?_⟩
      rw [← Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2]
      exact hq.radical_le_iff.mpr hp
    · exact (hq.ne_top (top_unique hp)).elim
  · rintro ⟨p, hp, ha, hpq⟩
    let p' : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J :=
      ⟨⟨p, hp.1.1⟩, hp⟩
    refine ⟨p', ?_⟩
    rw [if_pos ha]
    exact (Ideal.le_radical.trans
      (Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p'.1 p'.2).le).trans hpq

theorem mem_cutLocus_iff (J I : Ideal M.CoordinateRing) (U : MaximalOpenLocus M)
    (m : MaximalSpectrum M.CoordinateRing) :
    m ∈ cutLocus M J I U ↔ m ∈ U ∧
      Hilbert.IsRelevant K M.factorCount M.ambientDimension m.asIdeal ∧
      ∀ p ∈ J.minimalPrimes,
        p ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → ¬ p ≤ m.asIdeal := by
  change (m ∈ U ∧ ¬ Hilbert.irrelevantIdeal K M.factorCount M.ambientDimension ≤ m.asIdeal) ∧
    ¬ retainedPart M J I ≤ m.asIdeal ↔ _
  rw [retainedPart_le_prime_iff M J I _ m.isMaximal.isPrime]
  simp only [not_exists, not_and]
  exact and_assoc

theorem cutLocus_le (J I : Ideal M.CoordinateRing) (U : MaximalOpenLocus M) :
    cutLocus M J I U ≤ U := inf_le_left.trans inf_le_left


end PhilipponMultiplicity.SectionThreeSupport

namespace PhilipponMultiplicity.SectionThreeSupport
open ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A new isolated component cannot contain a retained old component: both
would be minimal primes of the same cut. Jacobson avoidance then puts it
on the actual current locus, possibly with a new maximal-ideal witness. -/
theorem new_component_meets_cutLocus (J I : Ideal M.CoordinateRing) (hJI : J ≤ I)
    (P : M.CoordinateRing) (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (q : Ideal M.CoordinateRing) (hq : q ∈ (J ⊔ Ideal.span {P}).minimalPrimes)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q)
    (hU : Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U)
    (hnew : ¬ (q ∈ J.minimalPrimes ∧
      q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I))) :
    Hilbert.MeetsOpen K M.factorCount M.ambientDimension q (cutLocus M J I U) := by
  have hret : ¬ retainedPart M J I ≤ q := by
    rw [retainedPart_le_prime_iff M J I q hq.1.1]
    rintro ⟨p, hp, ha, hpq⟩
    have hpcut := (component_partition_cut M J I hJI P hPI).2 p hp ha
    have heq : p = q := le_antisymm hpq (hq.2 hpcut.1 hpq)
    exact hnew (heq ▸ And.intro hp ha)
  unfold cutLocus
  apply (meetsOpen_inf_away_iff M q hq.1.1 _ _).mpr
  refine ⟨?_, hret⟩
  exact (meetsOpen_inf_away_iff M q hq.1.1 U _).mpr ⟨hU, hrel⟩


end PhilipponMultiplicity.SectionThreeSupport

namespace PhilipponMultiplicity.ComponentDegree
variable {ι : Type*} [Fintype ι]

theorem eval_nonneg_of_coeff_nonneg (F : MvPolynomial ι ℚ)
    (hF : ∀ e, 0 ≤ coeff e F) (d : ι → ℕ) : 0 ≤ eval (fun i => (d i : ℚ)) F := by
  classical
  rw [eval_eq]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hF e)
    (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)

end PhilipponMultiplicity.ComponentDegree

namespace PhilipponMultiplicity.PrimaryComponentSupport
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem degreeValue_nonneg (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (D : M.FactorIndex → ℕ) :
    0 ≤ Hilbert.degreeValue K M.factorCount M.ambientDimension I D := by
  unfold Hilbert.degreeValue Hilbert.degreeForm
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
  apply mul_nonneg (Nat.cast_nonneg _)
  exact ComponentDegree.eval_nonneg_of_coeff_nonneg _
    (multigraded_hilbert_polynomial_top_coefficients K M I hI).1 D

end PhilipponMultiplicity.PrimaryComponentSupport

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem primaryComponent_degreeValue_antitone (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I) (q : PrimeSpectrum M.CoordinateRing)
    (hqJ : q.asIdeal ∈ J.minimalPrimes) (hqI : q.asIdeal ∈ I.minimalPrimes)
    (D : M.FactorIndex → ℕ) :
    degreeValue K M.factorCount M.ambientDimension
        (primaryComponent K M.factorCount M.ambientDimension I q) D ≤
      degreeValue K M.factorCount M.ambientDimension
        (primaryComponent K M.factorCount M.ambientDimension J q) D := by
  have hJh := primaryComponent_homogeneous M J hJ q hqJ
  have hIh := primaryComponent_homogeneous M I hI q hqI
  have hle : primaryComponent K M.factorCount M.ambientDimension J q ≤
      primaryComponent K M.factorCount M.ambientDimension I q :=
    Ideal.comap_mono (Ideal.map_mono hJI)
  have hdim := idealDimension_eq_of_radical_eq M _ _ hJh hIh
    ((primaryComponent_radical K M.factorCount M.ambientDimension J q hqJ).trans
      (primaryComponent_radical K M.factorCount M.ambientDimension I q hqI).symm)
  exact degreeValue_antitone_of_dimension_eq M _ _ hJh hIh hle hdim D

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.PrimaryCut
open SectionThree SectionThreeSupport ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

abbrev MinComponent (J : Ideal M.CoordinateRing) :=
  Hilbert.MinimalComponent K M.factorCount M.ambientDimension J

abbrev primary (J : Ideal M.CoordinateRing) (p : PrimeSpectrum M.CoordinateRing) :=
  Hilbert.primaryComponent K M.factorCount M.ambientDimension J p

/-- A literal intersection of selected canonical isolated primary components. -/
def selectedIntersection (J : Ideal M.CoordinateRing) (s : MinComponent M J → Prop) :
    Ideal M.CoordinateRing := ⨅ p : {p : MinComponent M J // s p}, primary M J p.1.1

theorem le_selectedIntersection (J : Ideal M.CoordinateRing) (s : MinComponent M J → Prop) :
    J ≤ selectedIntersection M J s :=
  le_iInf fun _ => Ideal.le_comap_map

theorem selectedIntersection_le (J : Ideal M.CoordinateRing) (s : MinComponent M J → Prop)
    (p : MinComponent M J) (hp : s p) : selectedIntersection M J s ≤ primary M J p.1 :=
  iInf_le (fun q : {q : MinComponent M J // s q} => primary M J q.1.1) ⟨p,hp⟩

theorem primary_le_prime (J : Ideal M.CoordinateRing) (p : MinComponent M J) :
    primary M J p.1 ≤ p.1.asIdeal :=
  Ideal.le_radical.trans (Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2).le

theorem selectedIntersection_le_prime_iff (J : Ideal M.CoordinateRing)
    (s : MinComponent M J → Prop) (q : Ideal M.CoordinateRing) (hq : q.IsPrime) :
    selectedIntersection M J s ≤ q ↔ ∃ p : MinComponent M J, s p ∧ p.1.asIdeal ≤ q := by
  rw [selectedIntersection, finite_iInf_le_prime _ q hq]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.1, p.2, ?_⟩
    rw [← Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1.1 p.1.2]
    exact hq.radical_le_iff.mpr hp
  · rintro ⟨p, hp, hpq⟩
    exact ⟨⟨p,hp⟩, (primary_le_prime M J p).trans hpq⟩

theorem selectedIntersection_minimalPrimes (J : Ideal M.CoordinateRing)
    (s : MinComponent M J → Prop) (q : Ideal M.CoordinateRing) :
    q ∈ (selectedIntersection M J s).minimalPrimes ↔
      ∃ p : MinComponent M J, s p ∧ p.1.asIdeal = q := by
  constructor
  · intro hq
    obtain ⟨p, hp, hpq⟩ := (selectedIntersection_le_prime_iff M J s q hq.1.1).mp hq.1.2
    have hNp := (selectedIntersection_le M J s p hp).trans (primary_le_prime M J p)
    exact ⟨p,hp,le_antisymm hpq (hq.2 ⟨p.1.isPrime,hNp⟩ hpq)⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p.1.isPrime, (selectedIntersection_le M J s p hp).trans (primary_le_prime M J p)⟩, ?_⟩
    intro q hq hqp
    exact p.2.2 ⟨hq.1,(le_selectedIntersection M J s).trans hq.2⟩ hqp

theorem selectedIntersection_homogeneous (J : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (s : MinComponent M J → Prop) :
    IsMultihomogeneousIdeal M (selectedIntersection M J s) := by
  intro f hf d
  simp only [selectedIntersection, Submodule.mem_iInf] at hf ⊢
  intro p
  exact Hilbert.primaryComponent_homogeneous M J hJ p.1.1 p.1.2 f
    (hf p) d

theorem selectedIntersection_primaryComponent (J : Ideal M.CoordinateRing)
    (s : MinComponent M J → Prop) (p : MinComponent M J) (hp : s p) :
    primary M (selectedIntersection M J s) p.1 = primary M J p.1 := by
  classical
  let A := Localization.AtPrime p.1.asIdeal
  let f := algebraMap M.CoordinateRing A
  have hmap : (selectedIntersection M J s).map f = (primary M J p.1).map f := by
    apply le_antisymm (Ideal.map_mono (selectedIntersection_le M J s p hp))
    change (primary M J p.1).map f ≤ (⨅ q : {q : MinComponent M J // s q}, primary M J q.1.1).map f
    rw [RegularCutSupport.localization_map_iInf p.1.asIdeal.primeCompl A]
    apply le_iInf
    intro q
    by_cases hqp : q.1 = p
    · subst hqp
      exact le_rfl
    · have hn : ¬ primary M J q.1.1 ≤ p.1.asIdeal := by
        intro h
        have hr : q.1.1.asIdeal ≤ p.1.asIdeal := by
          rw [← Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J q.1.1 q.1.2]
          exact p.1.isPrime.radical_le_iff.mpr h
        apply hqp
        apply Subtype.ext
        apply PrimeSpectrum.ext
        exact le_antisymm hr (p.2.2 q.1.2.1 hr)
      rw [IsLocalization.AtPrime.map_eq_top_of_not_le (S := A) hn]
      exact le_top
  change ((selectedIntersection M J s).map f).comap f = primary M J p.1
  rw [hmap]
  change (((J.map f).comap f).map f).comap f = (J.map f).comap f
  rw [IsLocalization.map_under p.1.asIdeal.primeCompl]

def selectedComponentEquiv (J : Ideal M.CoordinateRing) (s : MinComponent M J → Prop) :
    {p : MinComponent M J // s p} ≃ MinComponent M (selectedIntersection M J s) := by
  classical
  let f : {p : MinComponent M J // s p} → MinComponent M (selectedIntersection M J s) :=
    fun p => ⟨p.1.1,(selectedIntersection_minimalPrimes M J s p.1.1.asIdeal).mpr ⟨p.1,p.2,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : MinComponent M (selectedIntersection M J s) => r.1) hpq
  · intro q
    obtain ⟨p,hp,heq⟩ := (selectedIntersection_minimalPrimes M J s q.1.asIdeal).mp q.2
    refine ⟨⟨p,hp⟩, ?_⟩
    apply Subtype.ext
    exact PrimeSpectrum.ext heq

theorem selectedIntersection_equidimensional (J : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (s : MinComponent M J → Prop) (c : ℕ)
    (hdim : ∀ p, s p → idealDimension M p.1.asIdeal = c)
    (q : Ideal M.CoordinateRing) (hq : q ∈ (selectedIntersection M J s).minimalPrimes)
    (hr : Hilbert.IsRelevant K M.factorCount M.ambientDimension q) :
    idealDimension M q = idealDimension M (selectedIntersection M J s) := by
  have hN := selectedIntersection_homogeneous M J hJ s
  obtain ⟨p,hp,rfl⟩ := (selectedIntersection_minimalPrimes M J s q).mp hq
  apply le_antisymm
  · exact Hilbert.idealDimension_antitone M _ _ hN
      (Hilbert.minimalPrime_homogeneous M J p.1.asIdeal hJ p.2) hq.1.2
  · rw [hdim p hp]
    have hnon : IsNontrivialIdeal M (selectedIntersection M J s) := fun h =>
      hr (h.trans (p.1.isPrime.radical_le_iff.mpr hq.1.2))
    obtain ⟨r,hrmin,_,hrdim⟩ := Hilbert.exists_relevant_minimalPrime_dimension_eq M _ hN hnon
    obtain ⟨t,ht,rfl⟩ := (selectedIntersection_minimalPrimes M J s r).mp hrmin
    rw [← hrdim, hdim t ht]

/-- The degree of a relevant pure-dimensional primary slice is the sum of
the actual degrees of the selected original primary components. -/
theorem selectedIntersection_degree (J : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (s : MinComponent M J → Prop) (c : ℕ)
    (hrel : ∀ p, s p → Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal)
    (hdim : ∀ p, s p → idealDimension M p.1.asIdeal = c) (D : M.FactorIndex → ℕ) :
    idealDegreeValue M (selectedIntersection M J s) D = (by
      classical
      letI := Fintype.ofFinite {p : MinComponent M J // s p}
      exact ∑ p : {p : MinComponent M J // s p}, idealDegreeValue M (primary M J p.1.1) D) := by
  classical
  let N := selectedIntersection M J s
  letI := Fintype.ofFinite (MinComponent M N)
  letI := Fintype.ofFinite {p : MinComponent M J // s p}
  have hN := selectedIntersection_homogeneous M J hJ s
  have hr (q : MinComponent M N) : Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal := by
    obtain ⟨p,hp,heq⟩ := (selectedIntersection_minimalPrimes M J s q.1.asIdeal).mp q.2
    exact heq ▸ hrel p hp
  calc
    _ = ∑ q : MinComponent M N, idealDegreeValue M (primary M N q.1) D := by
      rw [Hilbert.component_length_formula M N hN D]
      unfold topComponentLengthSum
      apply Finset.sum_congr rfl
      intro q _
      rw [if_pos ⟨hr q,selectedIntersection_equidimensional M J hJ s c hdim q.1.asIdeal q.2 (hr q)⟩]
      exact (Hilbert.primaryComponent_degreeValue_eq_localLength M N hN q.1 q.2 (hr q) D).symm
    _ = _ := by
      symm
      apply Fintype.sum_equiv (selectedComponentEquiv M J s)
      intro p
      exact congrArg (fun A => idealDegreeValue M A D)
        (selectedIntersection_primaryComponent M J s p.1 p.2).symm

end PhilipponMultiplicity.PrimaryCut

namespace PhilipponMultiplicity.PrimaryCut
open SectionThree SectionThreeSupport ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

def sliceSelection (J I : Ideal M.CoordinateRing) (U : MaximalOpenLocus M) (c : ℕ)
    (p : MinComponent M J) : Prop :=
  Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal ∧
  p.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) ∧
  Hilbert.MeetsOpen K M.factorCount M.ambientDimension p.1.asIdeal (cutLocus M J I U) ∧
  idealDimension M p.1.asIdeal = c

def primarySlice (J I : Ideal M.CoordinateRing) (U : MaximalOpenLocus M) (c : ℕ) :
    Ideal M.CoordinateRing := selectedIntersection M J (sliceSelection M J I U c)

theorem primarySlice_regular (J I : Ideal M.CoordinateRing) (U : MaximalOpenLocus M)
    (c : ℕ) (P : M.CoordinateRing)
    (havoid : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → P ∉ q) :
    IsRegular (Ideal.Quotient.mk (primarySlice M J I U c) P) := by
  classical
  apply (Commute.isRegular_iff (fun y => mul_comm _ y)).mpr
  apply isLeftRegular_of_non_zero_divisor
  intro z hz
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hPr : P * r ∈ primarySlice M J I U c := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hz
  simp only [primarySlice, selectedIntersection, Submodule.mem_iInf] at hPr ⊢
  intro p
  have hn : P ∉ (primary M J p.1.1).radical := by
    rw [Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1.1 p.1.2]
    exact havoid p.1.1.asIdeal p.1.2 p.2.1 p.2.2.1
  exact ((Ideal.isPrimary_iff.mp
    (Hilbert.primaryComponent_isPrimary K M.factorCount M.ambientDimension J p.1.1 p.1.2)).2
      (mul_comm P r ▸ hPr p)).resolve_right hn

theorem old_below_new_slice (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (havoid : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → P ∉ q)
    (q : Ideal M.CoordinateRing) (hq : q ∈ (J ⊔ Ideal.span {P}).minimalPrimes)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q)
    (hU : Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U)
    (hnew : ¬ (q ∈ J.minimalPrimes ∧ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)))
    (p : MinComponent M J) (hpq : p.1.asIdeal ≤ q) :
    sliceSelection M J I U (idealDimension M q + 1) p := by
  have hr : Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal :=
    fun h => hrel (h.trans hpq)
  have hn : p.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) := by
    intro ha
    have hp' := (component_partition_cut M J I hJI P hPI).2 p.1.asIdeal p.2 ha
    have heq : p.1.asIdeal = q := le_antisymm hpq (hq.2 hp'.1 hpq)
    exact hnew (heq ▸ And.intro p.2 ha)
  have hq' : q ∈ (p.1.asIdeal ⊔ Ideal.span {P}).minimalPrimes := by
    refine ⟨⟨hq.1.1,sup_le hpq (le_sup_right.trans hq.1.2)⟩, ?_⟩
    intro r hr hrq
    exact hq.2 ⟨hr.1,sup_le (p.2.1.2.trans (le_sup_left.trans hr.2))
      (le_sup_right.trans hr.2)⟩ hrq
  have hd := Hilbert.relevant_hypersurface_component_dimension M p.1.asIdeal p.1.isPrime
    (Hilbert.minimalPrime_homogeneous M J p.1.asIdeal hJ p.2) P D hP
    (havoid p.1.asIdeal p.2 hr hn) q hq' hrel
  obtain ⟨m,hm,hqm⟩ := new_component_meets_cutLocus M J I hJI P hPI U q hq hrel hU hnew
  exact ⟨hr, hn, ⟨m,hm,hpq.trans hqm⟩, hd.symm⟩

/-- The dimension slice has the same actual localized ideal as the original
ideal at a new cut prime. CM excludes embedded components through this prime;
the hypersurface dimension theorem selects precisely the surviving dimension. -/
theorem map_eq_primarySlice_at_new (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (havoid : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → P ∉ q)
    (q : PrimeSpectrum M.CoordinateRing) (hq : q.asIdeal ∈ (J ⊔ Ideal.span {P}).minimalPrimes)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q.asIdeal)
    (hU : Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.asIdeal U)
    (hnew : ¬ (q.asIdeal ∈ J.minimalPrimes ∧
      q.asIdeal ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I))) :
    J.map (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal)) =
      (primarySlice M J I U (idealDimension M q.asIdeal + 1)).map
        (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal)) := by
  classical
  obtain ⟨m,hm,hqm⟩ := new_component_meets_cutLocus M J I hJI P hPI U q.asIdeal hq hrel hU hnew
  obtain ⟨E⟩ := exists_primaryDecomposition M J hJ
  let A := Localization.AtPrime q.asIdeal
  let f := algebraMap M.CoordinateRing A
  apply le_antisymm (Ideal.map_mono (le_selectedIntersection M J _))
  change (primarySlice M J I U (idealDimension M q.asIdeal + 1)).map f ≤ J.map f
  conv_rhs => rw [E.intersection_eq, RegularCutSupport.localization_map_iInf q.asIdeal.primeCompl A]
  apply le_iInf
  intro i
  by_cases hiq : E.component i ≤ q.asIdeal
  · have hrq := q.isPrime.radical_le_iff.mpr hiq
    have ha : (E.component i).radical ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ J) := by
      rw [E.associatedPrimes_eq M J]
      exact ⟨i,rfl⟩
    have hp := Hilbert.cohenMacaulayAt_associated_isMinimal M J m (hCM m hm) _ ha (hrq.trans hqm)
    let p : MinComponent M J := ⟨⟨(E.component i).radical,hp.1.1⟩,hp⟩
    have hs := old_below_new_slice M J I hJ hJI P D hP hPI U havoid q.asIdeal hq hrel hU hnew p hrq
    obtain ⟨j,hj,heq⟩ := PrimaryComponentSupport.primaryComponent_eq_decomposition M J E p.1 p.2
    have hji : j = i := E.radicals_injective hj
    subst j
    exact Ideal.map_mono ((selectedIntersection_le M J _ p hs).trans heq.le)
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le (S := A) hiq]
    exact le_top

/-- Comparison on actual primary ideals, not merely on their radicals.
A new primary cut component is exactly the corresponding component of the
cut of the selected dimension slice. -/
theorem new_primaryComponent_eq_slice (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (havoid : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → P ∉ q)
    (q : PrimeSpectrum M.CoordinateRing) (hq : q.asIdeal ∈ (J ⊔ Ideal.span {P}).minimalPrimes)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q.asIdeal)
    (hU : Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.asIdeal U)
    (hnew : ¬ (q.asIdeal ∈ J.minimalPrimes ∧
      q.asIdeal ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I))) :
    let N := primarySlice M J I U (idealDimension M q.asIdeal + 1)
    q.asIdeal ∈ (N ⊔ Ideal.span {P}).minimalPrimes ∧
      primary M (J ⊔ Ideal.span {P}) q = primary M (N ⊔ Ideal.span {P}) q := by
  let N := primarySlice M J I U (idealDimension M q.asIdeal + 1)
  have hJN : J ≤ N := le_selectedIntersection M J _
  obtain ⟨p,hp,hpq⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hq.1.2)
  let p' : MinComponent M J := ⟨⟨p,hp.1.1⟩,hp⟩
  have hs := old_below_new_slice M J I hJ hJI P D hP hPI U havoid q.asIdeal hq hrel hU hnew p' hpq
  have hNq : N ≤ q.asIdeal := ((selectedIntersection_le M J _ p' hs).trans (primary_le_prime M J p')).trans hpq
  refine ⟨minimalPrime_of_between hq (sup_le_sup hJN le_rfl)
    (sup_le hNq (le_sup_right.trans hq.1.2)), ?_⟩
  have heq := map_eq_primarySlice_at_new M J I hJ hJI P D hP hPI U hCM havoid q hq hrel hU hnew
  unfold primary Hilbert.primaryComponent
  simp only [Ideal.map_sup]
  rw [heq]

end PhilipponMultiplicity.PrimaryCut

namespace PhilipponMultiplicity.PrimaryCut
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

abbrev Active (J : Ideal M.CoordinateRing) (U : MaximalOpenLocus M) :=
  {p : MinComponent M J // Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal ∧
    Hilbert.MeetsOpen K M.factorCount M.ambientDimension p.1.asIdeal U}

theorem componentSum_eq_active (J : Ideal M.CoordinateRing) (U : MaximalOpenLocus M)
    (D : M.FactorIndex → ℕ) : componentHilbertSum M J U D = (by
      classical
      letI := Fintype.ofFinite (Active M J U)
      exact ∑ p : Active M J U, idealDegreeValue M (primary M J p.1.1) D) := by
  classical
  letI := Fintype.ofFinite (MinComponent M J)
  letI := Fintype.ofFinite (Active M J U)
  unfold componentHilbertSum Hilbert.componentSum
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem sum_le_of_injective {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (a : α → ℚ) (b : β → ℚ)
    (hle : ∀ x, a x ≤ b (f x)) (hn : ∀ y, 0 ≤ b y) :
    ∑ x, a x ≤ ∑ y, b y := by
  classical
  calc
    _ ≤ ∑ x, b (f x) := Finset.sum_le_sum (fun x _ => hle x)
    _ = ∑ y ∈ Finset.univ.image f, b y :=
      (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => hn y)

/-- A cover that compares actual primary degrees bounds the scheme-theoretic
component sum. An injective assignment counts each original component once. -/
theorem componentSum_le_cover {ι : Type*} [Fintype ι]
    (L : Ideal M.CoordinateRing) (B : ι → Ideal M.CoordinateRing)
    (hB : ∀ i, IsMultihomogeneousIdeal M (B i)) (U : MaximalOpenLocus M)
    (D : M.FactorIndex → ℕ)
    (hcover : ∀ q : MinComponent M L,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal →
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U →
      ∃ i, q.1.asIdeal ∈ (B i).minimalPrimes ∧
        idealDegreeValue M (primary M L q.1) D ≤ idealDegreeValue M (primary M (B i) q.1) D) :
    componentHilbertSum M L U D ≤ ∑ i, componentHilbertSum M (B i) U D := by
  classical
  letI := Fintype.ofFinite (Active M L U)
  letI (i : ι) := Fintype.ofFinite (Active M (B i) U)
  let idx (q : Active M L U) := (hcover q.1 q.2.1 q.2.2).choose
  let f : Active M L U → Σ i, Active M (B i) U := fun q =>
    ⟨idx q, ⟨⟨q.1.1,(hcover q.1 q.2.1 q.2.2).choose_spec.1⟩,q.2⟩⟩
  have hf : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Σ i, Active M (B i) U => z.2.1.1) h
  simp_rw [componentSum_eq_active M]
  rw [← Fintype.sum_sigma']
  exact sum_le_of_injective f hf _ _ (fun q => (hcover q.1 q.2.1 q.2.2).choose_spec.2)
    (fun q => PrimaryComponentSupport.degreeValue_nonneg M _
      (Hilbert.primaryComponent_homogeneous M (B q.1) (hB q.1) q.2.1.1 q.2.1.2) D)

theorem selectedIntersection_componentSum (J : Ideal M.CoordinateRing)
    (s : MinComponent M J → Prop) (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ)
    (hs : ∀ p, s p → Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal ∧
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension p.1.asIdeal U) :
    componentHilbertSum M (selectedIntersection M J s) U D = (by
      classical
      letI := Fintype.ofFinite {p : MinComponent M J // s p}
      exact ∑ p : {p : MinComponent M J // s p}, idealDegreeValue M (primary M J p.1.1) D) := by
  classical
  let N := selectedIntersection M J s
  letI := Fintype.ofFinite (MinComponent M N)
  letI := Fintype.ofFinite {p : MinComponent M J // s p}
  calc
    _ = ∑ q : MinComponent M N, idealDegreeValue M (primary M N q.1) D := by
      unfold componentHilbertSum Hilbert.componentSum
      apply Finset.sum_congr rfl
      intro q _
      obtain ⟨p,hp,heq⟩ := (selectedIntersection_minimalPrimes M J s q.1.asIdeal).mp q.2
      rw [if_pos (heq ▸ hs p hp)]
      rfl
    _ = _ := by
      symm
      apply Fintype.sum_equiv (selectedComponentEquiv M J s)
      intro p
      exact congrArg (fun A => idealDegreeValue M A D)
        (selectedIntersection_primaryComponent M J s p.1 p.2).symm

/-- Disjoint selections of active original components cannot exceed the
original component sum; this is the final finite grouping by dimension. -/
theorem selected_sums_le_componentSum {ι : Type*} [Fintype ι]
    (J : Ideal M.CoordinateRing) (hJ : IsMultihomogeneousIdeal M J)
    (s : ι → MinComponent M J → Prop) (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ)
    (hs : ∀ i p, s i p → Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal ∧
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension p.1.asIdeal U)
    (hdis : ∀ i j p, s i p → s j p → i = j) :
    (by
      classical
      letI (i : ι) := Fintype.ofFinite {p : MinComponent M J // s i p}
      exact ∑ i, ∑ p : {p : MinComponent M J // s i p}, idealDegreeValue M (primary M J p.1.1) D) ≤
      componentHilbertSum M J U D := by
  classical
  letI (i : ι) := Fintype.ofFinite {p : MinComponent M J // s i p}
  letI := Fintype.ofFinite (Active M J U)
  let T := Σ i, {p : MinComponent M J // s i p}
  let f : T → Active M J U := fun p => ⟨p.2.1,hs p.1 p.2.1 p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨i,p⟩ ⟨j,q⟩ h
    have hpq : p.1 = q.1 := congrArg (fun r : Active M J U => r.1) h
    have hij : i = j := hdis i j p.1 p.2 (hpq.symm ▸ q.2)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext hpq)
  rw [componentSum_eq_active M J U D, ← Fintype.sum_sigma']
  exact sum_le_of_injective f hf _ _ (fun _ => le_rfl)
    (fun p => PrimaryComponentSupport.degreeValue_nonneg M _
      (Hilbert.primaryComponent_homogeneous M J hJ p.1.1 p.1.2) D)

end PhilipponMultiplicity.PrimaryCut

namespace PhilipponMultiplicity.PrimaryCut
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

def retainedSelection (J I : Ideal M.CoordinateRing) (U : MaximalOpenLocus M)
    (p : MinComponent M J) : Prop :=
  Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal ∧
  Hilbert.MeetsOpen K M.factorCount M.ambientDimension p.1.asIdeal U ∧
  p.1.asIdeal ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)

/-- Bound the new components by cuts of their dimension slices and compare
the retained components with their original canonical primary ideals. -/
theorem cut_le_retained_add_slices (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (havoid : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → P ∉ q) :
    componentHilbertSum M (J ⊔ Ideal.span {P}) U D ≤
      componentHilbertSum M (selectedIntersection M J (retainedSelection M J I U)) U D +
      ∑ c : Fin (idealDimension M J + 1), idealDegreeValue M (primarySlice M J I U c.val) D := by
  classical
  let C := Fin (idealDimension M J + 1)
  let R := selectedIntersection M J (retainedSelection M J I U)
  let N (c : C) := primarySlice M J I U c.val
  let B : Option C → Ideal M.CoordinateRing := fun o =>
    o.elim R (fun c => N c ⊔ Ideal.span {P})
  have hNh (c : C) : IsMultihomogeneousIdeal M (N c) := selectedIntersection_homogeneous M J hJ _
  have hBh (o : Option C) : IsMultihomogeneousIdeal M (B o) := by
    cases o with
    | none => exact selectedIntersection_homogeneous M J hJ _
    | some c => exact Hilbert.homogeneous_sup_span M (N c) (hNh c) P D hP
  have hcover (q : MinComponent M (J ⊔ Ideal.span {P}))
      (hr : Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal)
      (hu : Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U) :
      ∃ o : Option C, q.1.asIdeal ∈ (B o).minimalPrimes ∧
        idealDegreeValue M (primary M (J ⊔ Ideal.span {P}) q.1) D ≤
          idealDegreeValue M (primary M (B o) q.1) D := by
    by_cases hold : q.1.asIdeal ∈ J.minimalPrimes ∧
        q.1.asIdeal ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)
    · let p : MinComponent M J := ⟨q.1,hold.1⟩
      have hs : retainedSelection M J I U p := ⟨hr,hu,hold.2⟩
      refine ⟨none, (selectedIntersection_minimalPrimes M J _ q.1.asIdeal).mpr ⟨p,hs,rfl⟩, ?_⟩
      change idealDegreeValue M (primary M (J ⊔ Ideal.span {P}) q.1) D ≤
        idealDegreeValue M (primary M R p.1) D
      rw [selectedIntersection_primaryComponent M J _ p hs]
      exact Hilbert.primaryComponent_degreeValue_antitone M J (J ⊔ Ideal.span {P}) hJ
        (Hilbert.homogeneous_sup_span M J hJ P D hP) le_sup_left q.1 hold.1 q.2 D
    · have hq := new_primaryComponent_eq_slice M J I hJ hJI P D hP hPI U hCM havoid
        q.1 q.2 hr hu hold
      letI : q.1.asIdeal.IsPrime := q.1.isPrime
      obtain ⟨p,hp,hpq⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans q.2.1.2)
      let p' : MinComponent M J := ⟨⟨p,hp.1.1⟩,hp⟩
      have hps := old_below_new_slice M J I hJ hJI P D hP hPI U havoid
        q.1.asIdeal q.2 hr hu hold p' hpq
      have hd := Hilbert.idealDimension_antitone M J p hJ
        (Hilbert.minimalPrime_homogeneous M J p hJ hp) hp.1.2
      have hpdim : idealDimension M p = idealDimension M q.1.asIdeal + 1 := hps.2.2.2
      let c : C := ⟨idealDimension M q.1.asIdeal + 1,by omega⟩
      refine ⟨some c,hq.1,?_⟩
      exact le_of_eq (congrArg (fun A => idealDegreeValue M A D) hq.2)
  have hnum (c : C) : componentHilbertSum M (N c ⊔ Ideal.span {P}) U D ≤
      idealDegreeValue M (N c) D := by
    apply componentSum_regular_cut_le_of_equidimensional M (N c) (hNh c)
      (fun q hq hr => selectedIntersection_equidimensional M J hJ _ c.val
        (fun p hp => hp.2.2.2) q hq hr) P D hP
      (primarySlice_regular M J I U c.val P havoid) U
  calc
    _ ≤ ∑ o : Option C, componentHilbertSum M (B o) U D :=
      componentSum_le_cover M (J ⊔ Ideal.span {P}) B hBh U D hcover
    _ = componentHilbertSum M R U D + ∑ c : C, componentHilbertSum M (N c ⊔ Ideal.span {P}) U D :=
      Fintype.sum_option (fun o : Option C => componentHilbertSum M (B o) U D)
    _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum (fun c _ => hnum c))

/-- All original components used by the preceding estimates form disjoint
selections: retained components and one discarded group per dimension. -/
theorem retained_add_slices_le (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M (selectedIntersection M J (retainedSelection M J I U)) U D +
      (∑ c : Fin (idealDimension M J + 1), idealDegreeValue M (primarySlice M J I U c.val) D) ≤
        componentHilbertSum M J U D := by
  classical
  let C := Fin (idealDimension M J + 1)
  let s : Option C → MinComponent M J → Prop := fun o =>
    o.elim (retainedSelection M J I U) (fun c => sliceSelection M J I U c.val)
  letI (o : Option C) := Fintype.ofFinite {p : MinComponent M J // s o p}
  have hs (o : Option C) (p : MinComponent M J) (hp : s o p) :
      Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal ∧
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension p.1.asIdeal U := by
    cases o with
    | none => exact ⟨hp.1,hp.2.1⟩
    | some c =>
      obtain ⟨m,hm,hpm⟩ := hp.2.2.1
      exact ⟨hp.1,⟨m,cutLocus_le M J I U hm,hpm⟩⟩
  have hdis (o v : Option C) (p : MinComponent M J) (ho : s o p) (hv : s v p) : o = v := by
    cases o with
    | none =>
      cases v with
      | none => rfl
      | some c => exact (hv.2.1 ho.2.2).elim
    | some c =>
      cases v with
      | none => exact (ho.2.1 hv.2.2).elim
      | some d => exact congrArg some (Fin.ext (ho.2.2.2.symm.trans hv.2.2.2))
  calc
    _ = (∑ p : {p : MinComponent M J // s none p}, idealDegreeValue M (primary M J p.1.1) D) +
        ∑ c : C, ∑ p : {p : MinComponent M J // s (some c) p}, idealDegreeValue M (primary M J p.1.1) D := by
      rw [selectedIntersection_componentSum M J (retainedSelection M J I U) U D
        (fun p hp => ⟨hp.1,hp.2.1⟩)]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      exact selectedIntersection_degree M J hJ _ c.val
        (fun p hp => hp.1) (fun p hp => hp.2.2.2) D
    _ = ∑ o : Option C, ∑ p : {p : MinComponent M J // s o p},
        idealDegreeValue M (primary M J p.1.1) D :=
      (Fintype.sum_option (fun o : Option C =>
        ∑ p : {p : MinComponent M J // s o p}, idealDegreeValue M (primary M J p.1.1) D)).symm
    _ ≤ _ := selected_sums_le_componentSum M J hJ s U D hs hdis

end PhilipponMultiplicity.PrimaryCut

namespace PhilipponMultiplicity.SectionThreeSupport
open PrimaryCut

theorem componentSum_cut_le_on_cutLocus
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (J I : Ideal M.CoordinateRing) (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (havoid : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → P ∉ q) :
    componentHilbertSum M (J ⊔ Ideal.span {P}) U D ≤
      componentHilbertSum M J U D := by
  exact (cut_le_retained_add_slices M J I hJ hJI P D hP hPI U hCM havoid).trans
    (retained_add_slices_le M J I hJ U D)

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (J I : Ideal M.CoordinateRing) (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (havoid : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → P ∉ q) :
    componentHilbertSum M (J ⊔ Ideal.span {P}) U D ≤
      componentHilbertSum M J U D := by
  exact PhilipponMultiplicity.SectionThreeSupport.componentSum_cut_le_on_cutLocus M J I hJ hJI P D hP hPI U hCM havoid
