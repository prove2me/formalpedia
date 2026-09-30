-- Prove2me | solution 1 for TranscendenceTheory.minimal_prime_primary_component
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T18:45:00.006987+00:00
-- url     : https://prove2.me/submissions/b187137a-c4ee-465f-ac9d-e9f9d9b08a2d

import Theorems.Thm_TranscendenceTheory_differential_prime_localization
import Mathlib.Tactic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.HopkinsLevitzki

noncomputable section
namespace TranscendenceTheory

private theorem uniform_separator
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I p : Ideal R) [p.IsPrime] :
    ∃ s : R, s ∉ p ∧ ∀ x ∈ (I.map (algebraMap R (Localization.AtPrime p))).under R,
      s * x ∈ I := by
  classical
  let J := (I.map (algebraMap R (Localization.AtPrime p))).under R
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp J.fg_of_isNoetherianRing
  have hgen : ∀ i, g i ∈ J := by
    intro i
    rw [← hg]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hden : ∀ i : Fin n, ∃ s : R, s ∉ p ∧ s * g i ∈ I := by
    intro i
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) I (g i)).mp (hgen i)
  choose d hd using hden
  let s : R := ∏ i, d i
  have hs : s ∉ p := by
    intro h
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact (hd i).1 hi
  refine ⟨s, hs, ?_⟩
  change J ≤ Submodule.comap (LinearMap.mulLeft R s) I
  rw [← hg]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change s * g i ∈ I
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  change s = d i * b at hb
  rw [hb]
  convert I.mul_mem_left b (hd i).2 using 1
  ring

private theorem primary_split
    {R : Type*} [CommRing R] (I J p : Ideal R)
    (hIJ : I ≤ J) (hJ : J.IsPrimary) (hrad : J.radical = p)
    (s : R) (hs : s ∉ p) (hsep : ∀ x ∈ J, s * x ∈ I) :
    ∃ K : Ideal R, ¬ K ≤ p ∧ I = J ⊓ K := by
  let K := I ⊔ Ideal.span {s}
  refine ⟨K, ?_, ?_⟩
  · intro h
    have hsK : s ∈ K := (show Ideal.span {s} ≤ K from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton s))
    exact hs (h hsK)
  · apply le_antisymm (le_inf hIJ le_sup_left)
    intro x hx
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx.2
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hv
    have hsa : a * s ∈ J := by
      have := J.sub_mem (huv ▸ hx.1) (hIJ hu)
      simpa [mul_comm] using this
    have ha : a ∈ J := ((Ideal.isPrimary_iff.mp hJ).2 hsa).resolve_right (hrad ▸ hs)
    rw [← huv]
    exact I.add_mem hu (hsep a ha)


end TranscendenceTheory

open TranscendenceTheory

theorem solution
    (R : Type*) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
    (D : Derivation ℚ R R) (I p : Ideal R) [p.IsPrime]
    (hp : p ∈ I.minimalPrimes) :
    ∃ J : Ideal R,
      J = (I.map (algebraMap R (Localization.AtPrime p))).under R ∧
      I ≤ J ∧ J.IsPrimary ∧ J.radical = p ∧
      J.map (algebraMap R (Localization.AtPrime p)) =
        I.map (algebraMap R (Localization.AtPrime p)) ∧
      (∃ K : Ideal R, ¬ K ≤ p ∧ I = J ⊓ K) ∧
      (∃ s : R, s ∉ p ∧ ∀ f ∈ J, s * f ∈ I) ∧
      Module.length (Localization.AtPrime p)
        ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≠ ⊤ ∧
      ∀ T : ℕ,
        (∀ f ∈ I, ∀ k ≤ T, (D^[k]) f ∈ p) ↔
        (∀ f ∈ J, ∀ k ≤ T, (D^[k]) f ∈ p) := by
  let S := Localization.AtPrime p
  let K := I.map (algebraMap R S)
  let J := K.under R
  have hrad : K.radical = IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes S p I hp,
      IsLocalization.AtPrime.map_eq_maximalIdeal p S]
  have hK : K.IsPrimary := Ideal.isPrimary_of_isMaximal_radical (hrad ▸ inferInstance)
  have hJ : J.IsPrimary := hK.comap (algebraMap R S)
  have hJrad : J.radical = p := by
    change (K.comap (algebraMap R S)).radical = p
    rw [← Ideal.comap_radical, hrad]
    exact IsLocalization.AtPrime.under_maximalIdeal S p
  have hmap : J.map (algebraMap R S) = K := IsLocalization.map_under p.primeCompl S K
  have hdim : Ring.KrullDimLE 0 (S ⧸ K) := by
    apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
    intro Q hQ
    rw [Ideal.minimalPrimes_eq_subsingleton hK, Set.mem_singleton_iff] at hQ
    rw [hQ, hrad]
    infer_instance
  let : IsArtinianRing (S ⧸ K) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let : IsArtinian S (S ⧸ K) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := K))
  have hfinite : Module.length S (S ⧸ K) ≠ ⊤ := Module.length_ne_top
  have hIJ : I ≤ J := Ideal.le_comap_map
  obtain ⟨s, hs, hsep⟩ := uniform_separator R I p
  refine ⟨J, rfl, hIJ, hJ, hJrad, hmap,
    primary_split I J p hIJ hJ hJrad s hs hsep,
    ⟨s, hs, hsep⟩, hfinite, ?_⟩
  obtain ⟨d, _, hjets⟩ := differential_prime_localization R D p
  intro T
  rw [hjets I T, hjets J T, hmap]
