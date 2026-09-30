-- Prove2me | solution 1 for PhilipponMultiplicity.RadicalIntersection.radical_componentSum_cut_le
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T10:41:45.447858+00:00
-- url     : https://prove2.me/submissions/2154f1ad-1393-452e-9b9d-092b24b20c0f

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Theorems.Thm_PhilipponMultiplicity_Hilbert_primaryComponent_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_eq_of_radical_eq
import Theorems.Thm_PhilipponMultiplicity_Hilbert_degreeValue_antitone_of_dimension_eq
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_le_degreeValue_of_equidimensional
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_regular_cut_le_of_equidimensional
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
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

namespace PhilipponMultiplicity.RadicalIntersection
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem reduced_primaryComponent (I : Ideal M.CoordinateRing)
    (q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I.radical) :
    Hilbert.primaryComponent K M.factorCount M.ambientDimension I.radical q.1 = q.1.asIdeal := by
  have hq : q.1.asIdeal ∈ I.minimalPrimes := by
    simpa only [Ideal.radical_minimalPrimes] using q.2
  change (I.radical.map (algebraMap M.CoordinateRing (Localization.AtPrime q.1.asIdeal))).comap
    (algebraMap M.CoordinateRing (Localization.AtPrime q.1.asIdeal)) = q.1.asIdeal
  rw [IsLocalization.map_radical q.1.asIdeal.primeCompl, Ideal.comap_radical]
  exact Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension I q.1 hq

theorem reduced_componentSum (I : Ideal M.CoordinateRing)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I.radical U D = (by
      classical
      letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
      exact ∑ q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I,
        if Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
          Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U then
          Hilbert.degreeValue K M.factorCount M.ambientDimension q.1.asIdeal D else 0) := by
  classical
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I.radical)
  let e : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I.radical ≃
      Hilbert.MinimalComponent K M.factorCount M.ambientDimension I :=
    Equiv.subtypeEquivRight fun q => by rw [Ideal.radical_minimalPrimes]
  unfold componentHilbertSum Hilbert.componentSum
  apply Fintype.sum_equiv e
  intro q
  rw [reduced_primaryComponent M I q]
  rfl

abbrev ActiveComponent (I : Ideal M.CoordinateRing) (U : MaximalOpenLocus M) :=
  {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I //
    Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
    Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U}

theorem reduced_componentSum_eq_active (I : Ideal M.CoordinateRing)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I.radical U D = (by
      classical
      letI := Fintype.ofFinite (ActiveComponent M I U)
      exact ∑ q : ActiveComponent M I U, idealDegreeValue M q.1.1.asIdeal D) := by
  classical
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
  letI := Fintype.ofFinite (ActiveComponent M I U)
  rw [reduced_componentSum M I U D, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem componentSum_radical_le (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (U : MaximalOpenLocus M)
    (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I.radical U D ≤ componentHilbertSum M I U D := by
  classical
  rw [reduced_componentSum M I U D]
  unfold componentHilbertSum Hilbert.componentSum
  apply Finset.sum_le_sum
  intro q _
  split_ifs with h
  · let Q := Hilbert.primaryComponent K M.factorCount M.ambientDimension I q.1
    have hQ := Hilbert.primaryComponent_homogeneous M I hI q.1 q.2
    have hq := Hilbert.minimalPrime_homogeneous M I q.1.asIdeal hI q.2
    have hr := Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension I q.1 q.2
    exact Hilbert.degreeValue_antitone_of_dimension_eq M Q q.1.asIdeal hQ hq
      (Ideal.le_radical.trans hr.le)
      (Hilbert.idealDimension_eq_of_radical_eq M Q q.1.asIdeal hQ hq
        (hr.trans q.1.isPrime.radical.symm)) D
  · exact le_rfl

private theorem sum_le_of_injective {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (a : α → ℚ) (b : β → ℚ)
    (heq : ∀ x, a x = b (f x)) (hn : ∀ y, 0 ≤ b y) :
    ∑ x, a x ≤ ∑ y, b y := by
  classical
  calc
    _ = ∑ x, b (f x) := Finset.sum_congr rfl (fun x _ => heq x)
    _ = ∑ y ∈ Finset.univ.image f, b y :=
      (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => hn y)

/-- A finite cover of the contributing minimal components bounds the reduced
degree sum. A component is assigned once even if several members contain it. -/
theorem radical_componentSum_le_cover {ι : Type*} [Fintype ι]
    (I : Ideal M.CoordinateRing) (J : ι → Ideal M.CoordinateRing)
    (hJ : ∀ i, IsMultihomogeneousIdeal M (J i)) (U : MaximalOpenLocus M)
    (hcover : ∀ q ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U →
      ∃ i, q ∈ (J i).minimalPrimes) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I.radical U D ≤ ∑ i, componentHilbertSum M (J i).radical U D := by
  classical
  letI := Fintype.ofFinite (ActiveComponent M I U)
  letI (i : ι) := Fintype.ofFinite (ActiveComponent M (J i) U)
  let idx (q : ActiveComponent M I U) :=
    (hcover q.1.1.asIdeal q.1.2 q.2.1 q.2.2).choose
  let f : ActiveComponent M I U → Σ i, ActiveComponent M (J i) U := fun q =>
    ⟨idx q, ⟨⟨q.1.1, (hcover q.1.1.asIdeal q.1.2 q.2.1 q.2.2).choose_spec⟩, q.2⟩⟩
  have hf : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Σ i, ActiveComponent M (J i) U => z.2.1.1) h
  simp_rw [reduced_componentSum_eq_active M]
  rw [← Fintype.sum_sigma']
  exact sum_le_of_injective f hf _ _ (fun _ => rfl) (fun q =>
    PrimaryComponentSupport.degreeValue_nonneg M q.2.1.1.asIdeal
      (Hilbert.minimalPrime_homogeneous M (J q.1) q.2.1.1.asIdeal (hJ q.1) q.2.1.2) D)

theorem radical_prime_cut_le (p : Ideal M.CoordinateRing) (hp : p.IsPrime)
    (hph : IsMultihomogeneousIdeal M p) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) (U : MaximalOpenLocus M) :
    componentHilbertSum M (p ⊔ Ideal.span {P}).radical U D ≤ idealDegreeValue M p D := by
  classical
  letI : p.IsPrime := hp
  have hequi : ∀ q ∈ p.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q = idealDimension M p := by
    intro q hq _
    have : q = p := by simpa only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] using hq
    rw [this]
  by_cases hmem : P ∈ p
  · have heq : p ⊔ Ideal.span {P} = p := sup_eq_left.mpr (by
      rwa [Ideal.span_singleton_le_iff_mem])
    rw [heq, hp.radical]
    exact componentSum_le_degreeValue_of_equidimensional M p hph hequi U D
  · exact (componentSum_radical_le M _ (Hilbert.homogeneous_sup_span M p hph P D hP) U D).trans
      (componentSum_regular_cut_le_of_equidimensional M p hph hequi P D hP
        (isRegular_iff_ne_zero.mpr (fun hz => hmem (Ideal.Quotient.eq_zero_iff_mem.mp hz))) U)

/-- A homogeneous hypersurface of degree D cannot increase the total reduced
component degree evaluated at D, on any open locus. -/
theorem radical_componentSum_cut_le (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) (U : MaximalOpenLocus M) :
    componentHilbertSum M (I ⊔ Ideal.span {P}).radical U D ≤
      componentHilbertSum M I.radical U D := by
  classical
  letI := Fintype.ofFinite (ActiveComponent M I U)
  let J (p : ActiveComponent M I U) := p.1.1.asIdeal ⊔ Ideal.span {P}
  have hJh (p : ActiveComponent M I U) : IsMultihomogeneousIdeal M (J p) :=
    Hilbert.homogeneous_sup_span M _ (Hilbert.minimalPrime_homogeneous M I _ hI p.1.2) P D hP
  have hcover (q : Ideal M.CoordinateRing) (hq : q ∈ (I ⊔ Ideal.span {P}).minimalPrimes)
      (hr : Hilbert.IsRelevant K M.factorCount M.ambientDimension q)
      (hu : Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U) :
      ∃ p, q ∈ (J p).minimalPrimes := by
    letI : q.IsPrime := hq.isPrime
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hq.le)
    have hpr : Hilbert.IsRelevant K M.factorCount M.ambientDimension p := fun h => hr (h.trans hpq)
    have hpu : Hilbert.MeetsOpen K M.factorCount M.ambientDimension p U := by
      obtain ⟨m, hm, hqm⟩ := hu
      exact ⟨m, hm, hpq.trans hqm⟩
    refine ⟨⟨⟨⟨p, hp.isPrime⟩, hp⟩, hpr, hpu⟩, ⟨hq.isPrime, ?_⟩, ?_⟩
    · exact sup_le hpq (le_sup_right.trans hq.le)
    · intro r hr hrq
      exact hq.2 ⟨hr.1, sup_le (hp.le.trans (le_sup_left.trans hr.2))
        (le_sup_right.trans hr.2)⟩ hrq
  refine (radical_componentSum_le_cover M _ J hJh U hcover D).trans ?_
  rw [reduced_componentSum_eq_active M I U D]
  apply Finset.sum_le_sum
  intro p _
  exact radical_prime_cut_le M p.1.1.asIdeal p.1.1.isPrime
    (Hilbert.minimalPrime_homogeneous M I _ hI p.1.2) P D hP U

end PhilipponMultiplicity.RadicalIntersection

end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) (U : MaximalOpenLocus M) :
    componentHilbertSum M (I ⊔ Ideal.span {P}).radical U D ≤
      componentHilbertSum M I.radical U D := by
  exact PhilipponMultiplicity.RadicalIntersection.radical_componentSum_cut_le M I hI P D hP U
