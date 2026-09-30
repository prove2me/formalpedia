-- Prove2me | solution 1 for TranscendenceTheory.finite_punctual_ideal_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T02:53:01.149555+00:00
-- url     : https://prove2.me/submissions/57fe1cd9-66e4-4979-9980-8be7da77f186

import Theorems.Thm_TranscendenceTheory_finite_zero_locus_quotient_geometry
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Localization.Submodule


noncomputable section

namespace TranscendenceTheory

open MvPolynomial

variable {K σ ι : Type*} [Field K] [IsAlgClosed K] [Finite σ] [Fintype ι]

omit [Fintype ι] in
private theorem punctual_ideals_coprime
    (I : ι → Ideal (MvPolynomial σ K)) (x : ι → σ → K)
    (hx : Function.Injective x) (hzero : ∀ i, zeroLocus K (I i) = {x i}) :
    Pairwise (Function.onFun IsCoprime I) := by
  have hrad (i : ι) : (I i).radical = vanishingIdeal K {x i} := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), hzero i]
  intro i j hij
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, hrad i, hrad j]
  have hne : vanishingIdeal K {x i} ≠ vanishingIdeal K {x j} := by
    intro h
    apply hij
    apply hx
    apply (finite_zero_locus_quotient_geometry K σ (I i)).2.1
    exact PrimeSpectrum.ext h
  rw [Ideal.IsMaximal.coprime_of_ne (inferInstance : (vanishingIdeal K {x i}).IsMaximal)
    (inferInstance : (vanishingIdeal K {x j}).IsMaximal) hne]
  simp

omit [IsAlgClosed K] in
private theorem coprime_quotient_dimension
    (R : Type*) [CommRing R] [Algebra K R] (I : ι → Ideal R)
    (hI : Pairwise (Function.onFun IsCoprime I)) [∀ i, Module.Finite K (R ⧸ I i)] :
    Module.Finite K (R ⧸ ⨅ i, I i) ∧
      Module.finrank K (R ⧸ ⨅ i, I i) = ∑ i, Module.finrank K (R ⧸ I i) := by
  let e := Ideal.quotientInfRingEquivPiQuotient I hI
  let a : (R ⧸ ⨅ i, I i) ≃ₐ[K] (∀ i, R ⧸ I i) :=
    { e with
      commutes' := by
        intro r
        ext i
        rfl }
  let : Module.Finite K (R ⧸ ⨅ i, I i) :=
    Module.Finite.of_injective a.toLinearMap a.injective
  exact ⟨inferInstance, a.toLinearEquiv.finrank_eq.trans (Module.finrank_pi_fintype K)⟩

omit [IsAlgClosed K] [Finite σ] in
private theorem zeroLocus_intersection_punctual
    (I : ι → Ideal (MvPolynomial σ K)) (x : ι → σ → K)
    (hzero : ∀ i, zeroLocus K (I i) = {x i}) :
    zeroLocus K (⨅ i, I i) = Set.range x := by
  classical
  ext z
  constructor
  · intro hz
    have hle : (⨅ i, I i) ≤ (pointToPoint (k := K) z).asIdeal :=
      pointToPoint_zeroLocus_le _ ⟨z, hz, rfl⟩
    have hle' : Finset.univ.inf I ≤ (pointToPoint (k := K) z).asIdeal := by
      simpa only [Finset.inf_univ_eq_iInf] using hle
    obtain ⟨i, hi, hI⟩ := (pointToPoint (k := K) z).isPrime.inf_le'.mp hle'
    have hzI : z ∈ zeroLocus K (I i) := by
      intro p hp
      exact (mem_vanishingIdeal_singleton_iff z p).mp (hI hp)
    rw [hzero i, Set.mem_singleton_iff] at hzI
    exact ⟨i, hzI.symm⟩
  · rintro ⟨i, rfl⟩
    apply zeroLocus_anti_mono (iInf_le I i)
    rw [hzero i]
    exact Set.mem_singleton _

private theorem coprime_localization_intersection
    (R : Type*) [CommRing R] (I : ι → Ideal R)
    (hI : Pairwise (Function.onFun IsCoprime I)) (i : ι)
    (p : Ideal R) [p.IsPrime] (hi : I i ≤ p) :
    (⨅ j, I j).map (algebraMap R (Localization.AtPrime p)) =
      (I i).map (algebraMap R (Localization.AtPrime p)) := by
  classical
  let A := Localization.AtPrime p
  have hother (j : ι) (hji : j ≠ i) : (I j).map (algebraMap R A) = ⊤ := by
    apply IsLocalization.map_eq_top_of_not_subset p.primeCompl A
    intro hjSet
    have hj : I j ≤ p := fun r hr => not_not.mp (hjSet hr)
    have htop : (⊤ : Ideal R) ≤ p := by
      rw [← (hI hji).sup_eq]
      exact sup_le hj hi
    exact (inferInstance : p.IsPrime).ne_top (top_le_iff.mp htop)
  have hmap : (⨅ j, I j).map (algebraMap R A) =
      ⨅ j, (I j).map (algebraMap R A) := by
    have he := map_finset_inf (IsLocalization.mapFrameHom p.primeCompl A) Finset.univ I
    rw [Finset.inf_univ_eq_iInf, Finset.inf_univ_eq_iInf] at he
    exact he
  change (⨅ j, I j).map (algebraMap R A) = _
  rw [hmap]
  apply le_antisymm (iInf_le _ i)
  apply le_iInf
  intro j
  by_cases hji : j = i
  · subst j; exact le_rfl
  · rw [hother j hji]
    exact le_top

/-- Distinct single-point schemes glue without losing local multiplicity;
the dimension of the glued quotient is exactly the sum of their dimensions. -/
theorem finite_punctual_ideal_gluing
    (K σ ι : Type*) [Field K] [IsAlgClosed K] [Finite σ] [Fintype ι]
    (I : ι → Ideal (MvPolynomial σ K)) (x : ι → σ → K)
    (hx : Function.Injective x) (hzero : ∀ i, zeroLocus K (I i) = {x i}) :
    zeroLocus K (⨅ i, I i) = Set.range x ∧
    Module.Finite K (MvPolynomial σ K ⧸ ⨅ i, I i) ∧
    Module.finrank K (MvPolynomial σ K ⧸ ⨅ i, I i) =
      ∑ i, Module.finrank K (MvPolynomial σ K ⧸ I i) ∧
    ∀ i, (⨅ j, I j).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal)) =
      (I i).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal)) := by
  have hI := punctual_ideals_coprime I x hx hzero
  let : ∀ i, Module.Finite K (MvPolynomial σ K ⧸ I i) := fun i =>
    (finite_zero_locus_quotient_geometry K σ (I i)).1.mpr (by
      rw [hzero i]
      exact Set.finite_singleton _)
  obtain ⟨hfin, hdim⟩ := coprime_quotient_dimension (K := K) (MvPolynomial σ K) I hI
  refine ⟨zeroLocus_intersection_punctual I x hzero, hfin, hdim, ?_⟩
  intro i
  apply coprime_localization_intersection (MvPolynomial σ K) I hI i
  apply pointToPoint_zeroLocus_le (I i)
  refine ⟨x i, ?_, rfl⟩
  rw [hzero i]
  exact Set.mem_singleton _

end TranscendenceTheory

noncomputable section
namespace TranscendenceTheory

/-- Thicken a chosen support prime only far enough to retain the original localization. -/
theorem exists_punctual_extension
    (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    (I : Ideal R) [Module.Finite K (R ⧸ I)] (p : Ideal R) [p.IsPrime]
    (hIp : I ≤ p) :
    ∃ J : Ideal R, I ≤ J ∧ J.radical = p ∧
      J.map (algebraMap R (Localization.AtPrime p)) =
        I.map (algebraMap R (Localization.AtPrime p)) := by
  let Rp := Localization.AtPrime p
  let Iloc := I.map (algebraMap R Rp)
  let : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite K _
  let : IsArtinianRing (Rp ⧸ Iloc) := IsArtinianRing.localization_artinian
    (Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl) _
  obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient Iloc
  have hn' : IsLocalRing.maximalIdeal Rp ^ (n + 1) ≤ Iloc :=
    (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn
  let J := I ⊔ p ^ (n + 1)
  have hJp : J ≤ p := sup_le hIp (Ideal.pow_le_self (by omega))
  have hrad : J.radical = p := by
    apply le_antisymm
    · exact (Ideal.radical_mono hJp).trans_eq (Ideal.IsPrime.radical (inferInstance : p.IsPrime))
    · calc
        p = (p ^ (n + 1)).radical := by
          rw [Ideal.radical_pow (I := p) (n := n + 1) (by omega), Ideal.IsPrime.radical (inferInstance : p.IsPrime)]
        _ ≤ J.radical := Ideal.radical_mono le_sup_right
  refine ⟨J, le_sup_left, hrad, ?_⟩
  change (I ⊔ p ^ (n + 1)).map (algebraMap R Rp) = Iloc
  rw [Ideal.map_sup, Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal p Rp]
  exact sup_eq_left.mpr hn'

open MvPolynomial

theorem zeroLocus_eq_singleton_of_radical_eq
    (K σ : Type*) [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (x : σ → K)
    (hrad : I.radical = (pointToPoint (k := K) x).asIdeal) :
    zeroLocus K I = {x} := by
  ext z
  constructor
  · intro hz
    have hI : I ≤ (pointToPoint (k := K) z).asIdeal :=
      pointToPoint_zeroLocus_le I ⟨z, hz, rfl⟩
    have hle : (pointToPoint (k := K) x).asIdeal ≤ (pointToPoint (k := K) z).asIdeal := by
      rw [← hrad]
      exact (pointToPoint (k := K) z).isPrime.radical_le_iff.mpr hI
    have he : (pointToPoint (k := K) x).asIdeal = (pointToPoint (k := K) z).asIdeal :=
      Ideal.IsMaximal.eq_of_le (inferInstance : (vanishingIdeal K {x}).IsMaximal)
        (pointToPoint (k := K) z).isPrime.ne_top hle
    exact ((finite_zero_locus_quotient_geometry K σ I).2.1 (PrimeSpectrum.ext he)).symm
  · rintro rfl
    intro p hp
    apply (mem_vanishingIdeal_singleton_iff z p).mp
    change p ∈ (pointToPoint (k := K) z).asIdeal
    rw [← hrad]
    exact Ideal.le_radical hp

/-- Extract the components at selected support points. Their total dimension can
only decrease when the unselected support is discarded. -/
theorem finite_punctual_ideal_extraction
    (K σ ι : Type*) [Field K] [IsAlgClosed K] [Finite σ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) [Module.Finite K (MvPolynomial σ K ⧸ I)]
    (x : ι → σ → K) (hx : Function.Injective x)
    (hxI : ∀ i, x i ∈ zeroLocus K I) :
    ∃ J : ι → Ideal (MvPolynomial σ K),
      (∀ i, I ≤ J i) ∧ (∀ i, zeroLocus K (J i) = {x i}) ∧
      (∀ i, (J i).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal)) =
        I.map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal))) ∧
      (∑ i, Module.finrank K (MvPolynomial σ K ⧸ J i)) ≤
        Module.finrank K (MvPolynomial σ K ⧸ I) := by
  classical
  have hp (i : ι) : I ≤ (pointToPoint (k := K) (x i)).asIdeal :=
    pointToPoint_zeroLocus_le I ⟨x i, hxI i, rfl⟩
  choose J hIJ hrad hmap using fun i => exists_punctual_extension K
    (MvPolynomial σ K) I (pointToPoint (k := K) (x i)).asIdeal (hp i)
  have hzero (i : ι) : zeroLocus K (J i) = {x i} :=
    zeroLocus_eq_singleton_of_radical_eq K σ (J i) (x i) (hrad i)
  obtain ⟨_, _, hdim, _⟩ := finite_punctual_ideal_gluing K σ ι J x hx hzero
  refine ⟨J, hIJ, hzero, hmap, ?_⟩
  rw [← hdim]
  have hle : I ≤ ⨅ i, J i := le_iInf hIJ
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := (Ideal.Quotient.factorₐ K hle).toLinearMap) (Ideal.Quotient.factor_surjective hle)

end TranscendenceTheory

noncomputable section
open MvPolynomial

open TranscendenceTheory MvPolynomial

theorem solution
    (K σ ι : Type*) [Field K] [IsAlgClosed K] [Finite σ] [Fintype ι]
    (x : ι → σ → K) (hx : Function.Injective x) :
    (∀ J : ι → Ideal (MvPolynomial σ K),
      (∀ i, zeroLocus K (J i) = {x i}) →
      zeroLocus K (⨅ i, J i) = Set.range x ∧
      Module.Finite K (MvPolynomial σ K ⧸ ⨅ i, J i) ∧
      Module.finrank K (MvPolynomial σ K ⧸ ⨅ i, J i) =
        ∑ i, Module.finrank K (MvPolynomial σ K ⧸ J i) ∧
      ∀ i, (⨅ j, J j).map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal)) =
        (J i).map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal))) ∧
    (∀ I : Ideal (MvPolynomial σ K), Module.Finite K (MvPolynomial σ K ⧸ I) →
      (∀ i, x i ∈ zeroLocus K I) →
      ∃ J : ι → Ideal (MvPolynomial σ K),
        (∀ i, I ≤ J i) ∧ (∀ i, zeroLocus K (J i) = {x i}) ∧
        (∀ i, (J i).map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal)) =
          I.map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime (pointToPoint (k := K) (x i)).asIdeal))) ∧
        (∑ i, Module.finrank K (MvPolynomial σ K ⧸ J i)) ≤
          Module.finrank K (MvPolynomial σ K ⧸ I)) := by
  refine ⟨fun J hJ => finite_punctual_ideal_gluing K σ ι J x hx hJ, ?_⟩
  intro I hfinite hxI
  let : Module.Finite K (MvPolynomial σ K ⧸ I) := hfinite
  exact finite_punctual_ideal_extraction K σ ι I x hx hxI
