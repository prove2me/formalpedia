-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.cutLocus_step
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T12:14:49.008742+00:00
-- url     : https://prove2.me/submissions/0a4b0f6e-a1cd-4840-9438-16099ec95f80

import Definitions.Def_PhilipponMultiplicity_CutLocus
import Mathlib.RingTheory.Lasker
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_meetsOpen_inf_away_iff
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_primaryDecomposition
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_component_partition_cut
import Theorems.Thm_PhilipponMultiplicity_Hilbert_cohenMacaulayAt_associated_isMinimal
import Theorems.Thm_PhilipponMultiplicity_Hilbert_cohenMacaulayAt_sup_span_of_isRegular
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Pointwise
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport
noncomputable section

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

namespace PhilipponMultiplicity.ComponentLength
variable {R : Type*} [CommRing R]
theorem localization_map_colon (S : Submonoid R) (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization S A] (I : Ideal R) (P : R) :
    (I.colon {P}).map (algebraMap R A) =
      (I.map (algebraMap R A)).colon {algebraMap R A P} := by
  ext z
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
  rw [IsLocalization.mk'_mem_map_algebraMap_iff, Submodule.mem_colon_singleton,
    smul_eq_mul, ← IsLocalization.mk'_one (M := S) (S := A) P,
    ← IsLocalization.mk'_mul, mul_one, IsLocalization.mk'_mem_map_algebraMap_iff]
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc]

end PhilipponMultiplicity.ComponentLength

namespace PhilipponMultiplicity.RegularCutSupport
open ComponentLength
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

/-- A nonzerodivisor modulo an ideal stays a nonzerodivisor in its localized
quotient. Singleton colons make this independent of quotient presentations. -/
theorem regular_localized_quotient (S : Submonoid R) (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization S A] (I : Ideal R) (P : R)
    (hreg : IsRegular (Ideal.Quotient.mk I P)) :
    IsRegular (Ideal.Quotient.mk (I.map (algebraMap R A)) (algebraMap R A P)) := by
  have hcolon : I.colon {P} = I := by
    ext r
    simp only [Submodule.mem_colon_singleton, smul_eq_mul]
    constructor
    · intro hr
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply hreg.2
      simpa only [zero_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] using hr
    · exact fun hr => I.mul_mem_right P hr
  have hcolonA : (I.map (algebraMap R A)).colon {algebraMap R A P} =
      I.map (algebraMap R A) := by
    rw [← localization_map_colon S A I P, hcolon]
  apply (Commute.isRegular_iff (fun y => mul_comm _ y)).mpr
  apply isLeftRegular_of_non_zero_divisor
  intro z hz
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← hcolonA]
  apply Submodule.mem_colon_singleton.mpr
  rw [smul_eq_mul, mul_comm]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_mul]
  exact hz

end PhilipponMultiplicity.RegularCutSupport

namespace PhilipponMultiplicity.SectionThreeSupport
open RegularCutSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The regular component cut from the descending induction preserves the
Cohen--Macaulay locus because the component quotient agrees there with the
original quotient. No global regularity on the original quotient is required. -/
theorem locallyCohenMacaulayOn_sup_span_of_component_cut
    (I J : Ideal M.CoordinateRing) (P : M.CoordinateRing) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M I U)
    (heq : ∀ m : MaximalSpectrum M.CoordinateRing, m ∈ U →
      I.map (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal)) =
      J.map (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal)))
    (hreg : IsRegular (Ideal.Quotient.mk J P)) :
    IsLocallyCohenMacaulayOn M (I ⊔ Ideal.span {P}) U := by
  intro m hm
  apply Hilbert.cohenMacaulayAt_sup_span_of_isRegular M I m P (hCM m hm)
  rw [heq m hm]
  exact regular_localized_quotient m.asIdeal.primeCompl (Localization.AtPrime m.asIdeal) J P hreg


end PhilipponMultiplicity.SectionThreeSupport

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

/-- Fact C makes the source's open sets decrease after each cut. -/
theorem cutLocus_cut_le (J I : Ideal M.CoordinateRing) (hJI : J ≤ I)
    (P : M.CoordinateRing) (hPI : P ∈ I) (U : MaximalOpenLocus M) :
    cutLocus M (J ⊔ Ideal.span {P}) I U ≤ cutLocus M J I U := by
  intro m hm
  rcases (mem_cutLocus_iff M _ _ _ m).mp hm with ⟨hmU, hr, ha⟩
  refine (mem_cutLocus_iff M _ _ _ m).mpr ⟨hmU, hr, ?_⟩
  intro p hp hassoc
  exact ha p ((component_partition_cut M J I hJI P hPI).2 p hp hassoc) hassoc

/-- On the actual current locus, local CM excludes embedded components and
the removed support excludes retained and irrelevant components. Thus the
localized ideal is exactly the discarded relevant primary intersection. -/
theorem map_eq_discardedRelevantPart (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (m : MaximalSpectrum M.CoordinateRing) (hm : m ∈ cutLocus M J I U) :
    J.map (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal)) =
      (discardedRelevantPart M J I).map
        (algebraMap M.CoordinateRing (Localization.AtPrime m.asIdeal)) := by
  classical
  obtain ⟨D⟩ := exists_primaryDecomposition M J hJ
  let A := Localization.AtPrime m.asIdeal
  let f := algebraMap M.CoordinateRing A
  apply le_antisymm
  · apply Ideal.map_mono
    apply le_iInf
    intro q
    exact Ideal.le_comap_map
  · change (discardedRelevantPart M J I).map f ≤ J.map f
    conv_rhs => rw [D.intersection_eq, localization_map_iInf m.asIdeal.primeCompl A]
    apply le_iInf
    intro i
    by_cases him : D.component i ≤ m.asIdeal
    · have hrm := m.isMaximal.isPrime.radical_le_iff.mpr him
      have ha : (D.component i).radical ∈
          associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ J) := by
        rw [D.associatedPrimes_eq M J]
        exact ⟨i, rfl⟩
      have hp := Hilbert.cohenMacaulayAt_associated_isMinimal M J m (hCM m hm) _ ha hrm
      rcases (mem_cutLocus_iff M J I U m).mp hm with ⟨_, hrel, hret⟩
      have hr : Hilbert.IsRelevant K M.factorCount M.ambientDimension
          (D.component i).radical := fun h => hrel (h.trans hrm)
      have hn : (D.component i).radical ∉
          associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) :=
        fun h => hret _ hp h hrm
      let p : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J :=
        ⟨⟨(D.component i).radical, hp.1.1⟩, hp⟩
      obtain ⟨j, hj, heq⟩ := primaryComponent_eq_decomposition M J D p.1 p.2
      have hji : j = i := D.radicals_injective hj
      subst j
      apply Ideal.map_mono
      have hsel : discardedRelevantPart M J I ≤
          Hilbert.primaryComponent K M.factorCount M.ambientDimension J p.1 :=
        iInf_le (fun q : {q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J //
          Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
          q.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)} =>
          Hilbert.primaryComponent K M.factorCount M.ambientDimension J q.1.1) ⟨p, hr, hn⟩
      exact hsel.trans heq.le
    · rw [IsLocalization.AtPrime.map_eq_top_of_not_le (S := A) him]
      exact le_top

/-- The current and next ideals are CM on the actual shrinking source locus;
only regularity on discarded relevant components is needed. -/
theorem locallyCohenMacaulay_cutLocus_step (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (hreg : IsRegular (Ideal.Quotient.mk (discardedRelevantPart M J I) P)) :
    IsLocallyCohenMacaulayOn M (J ⊔ Ideal.span {P}) (cutLocus M J I U) ∧
    IsLocallyCohenMacaulayOn M (J ⊔ Ideal.span {P})
      (cutLocus M (J ⊔ Ideal.span {P}) I U) := by
  have hnext := locallyCohenMacaulayOn_sup_span_of_component_cut M J
    (discardedRelevantPart M J I) P (cutLocus M J I U) hCM
    (map_eq_discardedRelevantPart M J I hJ U hCM) hreg
  exact ⟨hnext, fun m hm => hnext m (cutLocus_cut_le M J I hJI P hPI U hm)⟩

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

/-- The paper's whole open-locus step, including both CM preservation and
the location of every new relevant isolated component. -/
theorem cutLocus_step (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (hreg : IsRegular (Ideal.Quotient.mk (discardedRelevantPart M J I) P)) :
    (cutLocus M (J ⊔ Ideal.span {P}) I U ≤ cutLocus M J I U) ∧
    IsLocallyCohenMacaulayOn M (J ⊔ Ideal.span {P}) (cutLocus M J I U) ∧
    IsLocallyCohenMacaulayOn M (J ⊔ Ideal.span {P})
      (cutLocus M (J ⊔ Ideal.span {P}) I U) ∧
    (∀ q ∈ (J ⊔ Ideal.span {P}).minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U →
      ¬ (q ∈ J.minimalPrimes ∧
        q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)) →
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q (cutLocus M J I U)) := by
  obtain ⟨hcurrent, hnext⟩ := locallyCohenMacaulay_cutLocus_step M J I hJ hJI P hPI U hCM hreg
  exact ⟨cutLocus_cut_le M J I hJI P hPI U, hcurrent, hnext,
    new_component_meets_cutLocus M J I hJI P hPI U⟩

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJI : J ≤ I)
    (P : M.CoordinateRing) (hPI : P ∈ I) (U : MaximalOpenLocus M)
    (hCM : IsLocallyCohenMacaulayOn M J (cutLocus M J I U))
    (hreg : IsRegular (Ideal.Quotient.mk (discardedRelevantPart M J I) P)) :
    (cutLocus M (J ⊔ Ideal.span {P}) I U ≤ cutLocus M J I U) ∧
    IsLocallyCohenMacaulayOn M (J ⊔ Ideal.span {P}) (cutLocus M J I U) ∧
    IsLocallyCohenMacaulayOn M (J ⊔ Ideal.span {P})
      (cutLocus M (J ⊔ Ideal.span {P}) I U) ∧
    (∀ q ∈ (J ⊔ Ideal.span {P}).minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U →
      ¬ (q ∈ J.minimalPrimes ∧
        q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)) →
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q (cutLocus M J I U)) := by
  exact PhilipponMultiplicity.SectionThreeSupport.cutLocus_step M J I hJ hJI P hPI U hCM hreg
