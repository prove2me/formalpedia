-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.exists_descending_cut_chain
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T09:14:51.590584+00:00
-- url     : https://prove2.me/submissions/54aa6c99-f36d-482b-a165-fb378568ad4f

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_radical_componentSum_le_of_discarded_zero
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_dimensionSlice_mono
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_regular_component_cut
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_antitone
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_dimension_strict
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
noncomputable section

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

theorem finite_iInf_le_prime {R ι : Type*} [CommRing R] [Finite ι]
    (A : ι → Ideal R) (q : Ideal R) (hq : q.IsPrime) :
    (⨅ i, A i) ≤ q ↔ ∃ i, A i ≤ q := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Finset.mem_univ, true_and] using
    (hq.inf_le' (s := Finset.univ) (f := A))

end PhilipponMultiplicity.ComponentSelection

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

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem dimensionAtLeast_le_prime_iff (J q : Ideal M.CoordinateRing)
    (hq : q.IsPrime) (b : ℕ) :
    dimensionAtLeast M J b ≤ q ↔
      ∃ p : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J,
        Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal ∧
        b ≤ idealDimension M p.1.asIdeal ∧ p.1.asIdeal ≤ q := by
  classical
  unfold dimensionAtLeast
  rw [finite_iInf_le_prime]
  · constructor
    · rintro ⟨p, hp⟩
      split_ifs at hp with h
      · refine ⟨p, h.1, h.2, ?_⟩
        rw [← Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2]
        exact hq.radical_le_iff.mpr hp
      · exact (hq.ne_top (top_unique hp)).elim
    · rintro ⟨p, hr, hd, hp⟩
      refine ⟨p, ?_⟩
      rw [if_pos ⟨hr, hd⟩]
      exact (Ideal.le_radical.trans (le_of_eq
        (Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2))).trans hp
  · exact hq


end PhilipponMultiplicity.SectionThreeSupport

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Above the dimension bound for discarded components, the actual relevant
minimal-prime sets of the intermediate and final ideals agree. -/
theorem high_minimalPrimes_eq (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I) (b : ℕ)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ b)
    (q : Ideal M.CoordinateRing)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q)
    (hdim : b < idealDimension M q) :
    q ∈ J.minimalPrimes ↔ q ∈ I.minimalPrimes := by
  constructor
  · intro hq
    have hassoc : q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) := by
      by_contra hn
      exact (not_le_of_gt hdim) (hbound q hq hrel hn)
    exact minimalPrime_of_between hq hJI (le_associatedPrime hassoc)
  · intro hq
    letI := hq.1.1
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (hJI.trans hq.1.2)
    have hprel : Hilbert.IsRelevant K M.factorCount M.ambientDimension p :=
      fun h => hrel (h.trans hpq)
    have hpdim := Hilbert.idealDimension_antitone M p q
      (Hilbert.minimalPrime_homogeneous M J p hJ hp)
      (Hilbert.minimalPrime_homogeneous M I q hI hq) hpq
    have hassoc : p ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) := by
      by_contra hn
      have := hbound p hp hprel hn
      omega
    have heq : p = q := le_antisymm hpq (hq.2 ⟨hp.1.1, le_associatedPrime hassoc⟩ hpq)
    exact heq ▸ hp

/-- The geometric invariant in Proposition 3.3 follows from the actual
dimension bound on discarded relevant components. -/
theorem dimensionAtLeast_radical_eq_of_discarded_bound (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I) (b : ℕ)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ b)
    (c : ℕ) (hbc : b < c) :
    (dimensionAtLeast M J c).radical = (dimensionAtLeast M I c).radical := by
  apply radical_eq_of_prime_containment
  intro q hq
  rw [dimensionAtLeast_le_prime_iff M J q hq c,
    dimensionAtLeast_le_prime_iff M I q hq c]
  constructor
  · rintro ⟨p, hr, hd, hpq⟩
    have hp := (high_minimalPrimes_eq M J I hJ hI hJI b hbound p.1.asIdeal hr
      (hbc.trans_le hd)).mp p.2
    exact ⟨⟨p.1, hp⟩, hr, hd, hpq⟩
  · rintro ⟨p, hr, hd, hpq⟩
    have hp := (high_minimalPrimes_eq M J I hJ hI hJI b hbound p.1.asIdeal hr
      (hbc.trans_le hd)).mpr p.2
    exact ⟨⟨p.1, hp⟩, hr, hd, hpq⟩

/-- One avoiding cut lowers the dimension bound on every discarded relevant
component by one. Retained components are treated by minimality, not by an
assumed decomposition or numerical dimension formula. -/
theorem cut_discarded_dimension_le (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hPI : P ∈ I) (b : ℕ)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ b + 1)
    (havoid : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → P ∉ q) :
    ∀ q ∈ (J ⊔ Ideal.span {P}).minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ b := by
  intro q hq hrel hnot
  letI := hq.1.1
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hq.1.2)
  have hprel : Hilbert.IsRelevant K M.factorCount M.ambientDimension p :=
    fun h => hrel (h.trans hpq)
  have hPq : P ∈ q := hq.1.2
    ((le_sup_right : Ideal.span {P} ≤ J ⊔ Ideal.span {P})
      (Ideal.subset_span (Set.mem_singleton P)))
  have hpnot : p ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) := by
    intro ha
    have hcutp : J ⊔ Ideal.span {P} ≤ p := by
      apply sup_le hp.1.2
      rw [Ideal.span_singleton_le_iff_mem]
      exact le_associatedPrime ha hPI
    have heq : p = q := le_antisymm hpq (hq.2 ⟨hp.1.1, hcutp⟩ hpq)
    exact hnot (heq ▸ ha)
  have hne : p ≠ q := fun heq => havoid p hp hprel hpnot (heq ▸ hPq)
  have hlt := Hilbert.relevant_prime_dimension_strict M p q hp.1.1 hq.1.1
    (Hilbert.minimalPrime_homogeneous M J p hJ hp)
    (Hilbert.minimalPrime_homogeneous M (J ⊔ Ideal.span {P}) q
      (Hilbert.homogeneous_sup_span M J hJ P D hP) hq)
    hrel (lt_of_le_of_ne hpq hne)
  have := hbound p hp hprel hpnot
  omega

private def DiscardedBound (J I : Ideal M.CoordinateRing) (b : ℕ) : Prop :=
  ∀ q ∈ J.minimalPrimes, Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
    q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → idealDimension M q ≤ b

private def CutStep (I E : Ideal M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (J J' : Ideal M.CoordinateRing) (f : M.CoordinateRing) : Prop :=
  J' = J ⊔ Ideal.span {f} ∧ f ∈ E ∧ M.IsHomogeneous f D ∧
  (∀ q ∈ J.minimalPrimes, Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
    q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → f ∉ q) ∧
  IsRegular (Ideal.Quotient.mk
    (⨅ q : {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J //
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)},
      Hilbert.primaryComponent K M.factorCount M.ambientDimension J q.1.1) f)

theorem homogeneous_sup_equations (I₀ : Ideal M.CoordinateRing)
    (hI₀ : IsMultihomogeneousIdeal M I₀) (m : ℕ) (P : Fin m → M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    IsMultihomogeneousIdeal M (I₀ ⊔ Ideal.span (Set.range P)) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hIg : I₀.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I₀
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI₀ f hf d
  have hPg : (Ideal.span (Set.range P)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    rintro f ⟨j, rfl⟩
    obtain ⟨d, _, hd⟩ := hP j
    exact ⟨d, hd⟩
  intro f hf d
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem K w (hIg.sup hPg) hf d

private theorem exists_cut_chain_aux [Infinite K]
    (I₀ : Ideal M.CoordinateRing) (m : ℕ) (P : Fin m → M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (b : ℕ) (J : Ideal M.CoordinateRing) (hJ : IsMultihomogeneousIdeal M J)
    (hI₀J : I₀ ≤ J) (hJI : J ≤ I₀ ⊔ Ideal.span (Set.range P))
    (hb : DiscardedBound M J (I₀ ⊔ Ideal.span (Set.range P)) b) :
    ∃ C : ℕ → Ideal M.CoordinateRing, ∃ F : ℕ → M.CoordinateRing,
      C 0 = J ∧
      (∀ t ≤ b, IsMultihomogeneousIdeal M (C t) ∧ I₀ ≤ C t ∧
        C t ≤ I₀ ⊔ Ideal.span (Set.range P) ∧
        DiscardedBound M (C t) (I₀ ⊔ Ideal.span (Set.range P)) (b - t)) ∧
      (∀ t < b, CutStep M (I₀ ⊔ Ideal.span (Set.range P))
        (Ideal.span (Set.range P)) D (C t) (C (t + 1)) (F t)) := by
  induction b generalizing J with
  | zero =>
    refine ⟨fun _ => J, fun _ => 0, rfl, ?_, ?_⟩
    · intro t ht
      exact ⟨hJ, hI₀J, hJI, by simpa using hb⟩
    · intro t ht
      omega
  | succ b ih =>
    let I := I₀ ⊔ Ideal.span (Set.range P)
    let S := {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J //
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)}
    obtain ⟨f, hf, hfh, hfa, hfr⟩ := exists_regular_component_cut M I₀ J hI₀J m P D hP hJI
      (fun q : S => q.1) (fun q => q.2.1) (fun q => q.2.2)
    have havoid (q : Ideal M.CoordinateRing) (hq : q ∈ J.minimalPrimes)
        (hr : Hilbert.IsRelevant K M.factorCount M.ambientDimension q)
        (hn : q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)) : f ∉ q :=
      hfa ⟨⟨⟨q, hq.1.1⟩, hq⟩, hr, hn⟩
    let J' := J ⊔ Ideal.span {f}
    have hJ'h : IsMultihomogeneousIdeal M J' := Hilbert.homogeneous_sup_span M J hJ f D hfh
    have hI₀J' : I₀ ≤ J' := hI₀J.trans le_sup_left
    have hfI : f ∈ I := (le_sup_right : Ideal.span (Set.range P) ≤ I) hf
    have hJ'I : J' ≤ I := by
      apply sup_le hJI
      rwa [Ideal.span_singleton_le_iff_mem]
    have hb' : DiscardedBound M J' I b :=
      cut_discarded_dimension_le M J I hJ hJI f D hfh hfI b hb havoid
    obtain ⟨C, F, hC0, hC, hF⟩ := ih J' hJ'h hI₀J' hJ'I hb'
    refine ⟨fun t => Nat.casesOn t J C, fun t => Nat.casesOn t f F, rfl, ?_, ?_⟩
    · intro t ht
      cases t with
      | zero => exact ⟨hJ, hI₀J, hJI, by simpa using hb⟩
      | succ t => simpa only [Nat.succ_sub_succ_eq_sub] using hC t (by omega)
    · intro t ht
      cases t with
      | zero => exact ⟨hC0, hf, hfh, havoid, hfr⟩
      | succ t => exact hF t (by omega)

/-- Constructs the actual dimension-descending part of Proposition 3.3.
The chain contains a cuts, where a is the initial Hilbert dimension; every
equation has the prescribed degree and is regular on the discarded relevant
primary components. Numerical degree-sum bounds are separate assertions. -/
theorem exists_descending_cut_chain_core [Infinite K]
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    let I := I₀ ⊔ Ideal.span (Set.range P)
    let a := idealDimension M I₀
    ∃ J : ℕ → Ideal M.CoordinateRing, ∃ F : ℕ → M.CoordinateRing,
      J 0 = I₀ ∧
      (∀ t ≤ a, IsMultihomogeneousIdeal M (J t) ∧ I₀ ≤ J t ∧ J t ≤ I ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
          idealDimension M q ≤ a - t) ∧
        (∀ c, a - t < c →
          (dimensionAtLeast M (J t) c).radical = (dimensionAtLeast M I c).radical)) ∧
      (∀ t < a, J (t + 1) = J t ⊔ Ideal.span {F t} ∧
        F t ∈ Ideal.span (Set.range P) ∧ M.IsHomogeneous (F t) D ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → F t ∉ q) ∧
        IsRegular (Ideal.Quotient.mk
          (⨅ q : {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension (J t) //
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
            q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)},
            Hilbert.primaryComponent K M.factorCount M.ambientDimension (J t) q.1.1) (F t))) ∧
      (∀ b, dimensionSlice M (J a) b ≤ dimensionSlice M I b) := by
  let I := I₀ ⊔ Ideal.span (Set.range P)
  let a := idealDimension M I₀
  have hI : IsMultihomogeneousIdeal M I := homogeneous_sup_equations M I₀ hI₀ m P D hP
  have hb : DiscardedBound M I₀ I a := by
    intro q hq _ _
    exact Hilbert.idealDimension_antitone M I₀ q hI₀
      (Hilbert.minimalPrime_homogeneous M I₀ q hI₀ hq) hq.1.2
  obtain ⟨J, F, hJ0, hJ, hF⟩ := exists_cut_chain_aux M I₀ m P D hP a I₀ hI₀ le_rfl le_sup_left hb
  refine ⟨J, F, hJ0, ?_, hF, ?_⟩
  · intro t ht
    obtain ⟨hJh, hlow, hupp, hbound⟩ := hJ t ht
    exact ⟨hJh, hlow, hupp, hbound,
      dimensionAtLeast_radical_eq_of_discarded_bound M (J t) I hJh hI hupp (a - t) hbound⟩
  · intro b
    obtain ⟨hJh, _, hupp, hbound⟩ := hJ a le_rfl
    apply dimensionSlice_mono M (J a) I hJh hI hupp b
    exact dimensionAtLeast_radical_eq_of_discarded_bound M (J a) I hJh hI hupp (a - a)
      hbound (b + 1) (by omega)
/-- The finite geometric chain and the final radical component comparison.
The two per-cut degree-sum estimates and the scheme-theoretic endpoint
comparison remain separate parts of Proposition 3.3. -/
theorem exists_descending_cut_chain [Infinite K]
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    let I := I₀ ⊔ Ideal.span (Set.range P)
    let a := idealDimension M I₀
    ∃ J : ℕ → Ideal M.CoordinateRing, ∃ F : ℕ → M.CoordinateRing,
      J 0 = I₀ ∧
      (∀ t ≤ a, IsMultihomogeneousIdeal M (J t) ∧ I₀ ≤ J t ∧ J t ≤ I ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
          idealDimension M q ≤ a - t) ∧
        (∀ c, a - t < c →
          (dimensionAtLeast M (J t) c).radical = (dimensionAtLeast M I c).radical)) ∧
      (∀ t < a, J (t + 1) = J t ⊔ Ideal.span {F t} ∧
        F t ∈ Ideal.span (Set.range P) ∧ M.IsHomogeneous (F t) D ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → F t ∉ q) ∧
        IsRegular (Ideal.Quotient.mk
          (⨅ q : {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension (J t) //
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
            q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)},
            Hilbert.primaryComponent K M.factorCount M.ambientDimension (J t) q.1.1) (F t))) ∧
      (∀ b, dimensionSlice M (J a) b ≤ dimensionSlice M I b) ∧
      (∀ (U : MaximalOpenLocus M) (d : M.FactorIndex → ℕ),
        componentHilbertSum M I.radical U d ≤ componentHilbertSum M (J a).radical U d)  := by
  let I := I₀ ⊔ Ideal.span (Set.range P)
  let a := idealDimension M I₀
  obtain ⟨J, F, hJ0, hJ, hF, hslice⟩ := exists_descending_cut_chain_core M I₀ hI₀ m P D hP
  refine ⟨J, F, hJ0, hJ, hF, hslice, ?_⟩
  intro U d
  obtain ⟨hJh, _, hJI, hbound, _⟩ := hJ a le_rfl
  exact radical_componentSum_le_of_discarded_zero M (J a) I hJh
    (homogeneous_sup_equations M I₀ hI₀ m P D hP) hJI
    (by simpa only [a, I, Nat.sub_self] using hbound) U d

end PhilipponMultiplicity.SectionThreeSupport

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
[Infinite K]
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    let I := I₀ ⊔ Ideal.span (Set.range P)
    let a := idealDimension M I₀
    ∃ J : ℕ → Ideal M.CoordinateRing, ∃ F : ℕ → M.CoordinateRing,
      J 0 = I₀ ∧
      (∀ t ≤ a, IsMultihomogeneousIdeal M (J t) ∧ I₀ ≤ J t ∧ J t ≤ I ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
          idealDimension M q ≤ a - t) ∧
        (∀ c, a - t < c →
          (dimensionAtLeast M (J t) c).radical = (dimensionAtLeast M I c).radical)) ∧
      (∀ t < a, J (t + 1) = J t ⊔ Ideal.span {F t} ∧
        F t ∈ Ideal.span (Set.range P) ∧ M.IsHomogeneous (F t) D ∧
        (∀ q ∈ (J t).minimalPrimes,
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
          q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → F t ∉ q) ∧
        IsRegular (Ideal.Quotient.mk
          (⨅ q : {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension (J t) //
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
            q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)},
            Hilbert.primaryComponent K M.factorCount M.ambientDimension (J t) q.1.1) (F t))) ∧
      (∀ b, dimensionSlice M (J a) b ≤ dimensionSlice M I b) ∧
      (∀ (U : MaximalOpenLocus M) (d : M.FactorIndex → ℕ),
        componentHilbertSum M I.radical U d ≤ componentHilbertSum M (J a).radical U d)  := by
  exact PhilipponMultiplicity.SectionThreeSupport.exists_descending_cut_chain M I₀ hI₀ m P D hP
