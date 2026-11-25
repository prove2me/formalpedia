-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.sum_le_prod_geom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:36:18.326749+00:00
-- url     : https://prove2.me/submissions/112a4b0f-289f-45af-983a-fc88a5c65853

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable (K : Type*) [Field K] [NumberField K]
open ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
namespace ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
theorem _root_.solution {s : ℝ} (hs : 0 < s) (T : Finset (Ideal (𝓞 K))) :
    ∃ P : Finset (HeightOneSpectrum (𝓞 K)), ∃ B : ℕ,
      ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) ≤
        ∏ v ∈ P, ∑ k ∈ Finset.range (B + 1), ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) ^ k := by
  classical
  set f : Ideal (𝓞 K) → ℝ := fun I ↦ (Ideal.absNorm I : ℝ) ^ (-s) with hf
  have hf0 : ∀ I, 0 ≤ f I := fun I ↦ by positivity
  set T' := T.filter (· ≠ ⊥) with hT'
  have hT'ne : ∀ I ∈ T', I ≠ 0 := fun I hI ↦ (Finset.mem_filter.mp hI).2
  have hsumT : ∑ I ∈ T, f I = ∑ I ∈ T', f I := by
    rw [hT', Finset.sum_filter_of_ne]
    intro I _ hI hbot
    apply hI
    simp [hf, hbot, Ideal.absNorm_bot, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  have hS : (⋃ I ∈ (T' : Set (Ideal (𝓞 K))), {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ I}).Finite :=
    Set.Finite.biUnion T'.finite_toSet fun I hI ↦ Ideal.finite_factors (hT'ne I hI)
  set P := hS.toFinset with hP
  let cnt : HeightOneSpectrum (𝓞 K) → Ideal (𝓞 K) → ℕ := fun v I ↦
    (Associates.mk v.asIdeal).count (Associates.mk I).factors
  set B := T'.sup fun I ↦ P.sup fun v ↦ cnt v I with hB
  refine ⟨P, B, ?_⟩
  let g : (P → ℕ) → Ideal (𝓞 K) := fun e ↦ ∏ v : P, v.1.asIdeal ^ e v
  let t : P → Finset ℕ := fun _ ↦ Finset.range (B + 1)
  have hsub : T' ⊆ (Fintype.piFinset t).image g := by
    intro I hI
    refine Finset.mem_image.mpr ⟨fun v ↦ cnt v.1 I, ?_, ?_⟩
    · refine Fintype.mem_piFinset.mpr fun v ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
      exact le_trans (Finset.le_sup (f := fun v ↦ cnt v I) v.2)
        (Finset.le_sup (f := fun I ↦ P.sup fun v ↦ cnt v I) hI)
    · have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) ↦ v.maxPowDividing I) ⊆
          (P : Set _) := by
        intro v hv
        rw [hP, Set.Finite.coe_toFinset]
        refine Set.mem_biUnion hI ?_
        by_contra hnd
        apply hv
        have h0 : cnt v I = 0 := by
          by_contra h
          exact hnd ((Associates.count_ne_zero_iff_dvd (hT'ne I hI) v.irreducible).mp h)
        simp only [HeightOneSpectrum.maxPowDividing]
        rw [show (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 from h0, pow_zero]
      have := Ideal.finprod_heightOneSpectrum_factorization (hT'ne I hI)
      rw [finprod_eq_prod_of_mulSupport_subset _ hsupp] at this
      exact (Finset.prod_coe_sort P (fun v ↦ v.maxPowDividing I)).trans this
  have hgf : ∀ e : P → ℕ, f (g e) = ∏ v : P, ((Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s)) ^ e v := by
    intro e
    simp only [hf, g, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
    rw [← Real.finsetProd_rpow _ _ (fun _ _ ↦ by positivity)]
    exact Finset.prod_congr rfl fun v _ ↦ (Real.rpow_pow_comm (Nat.cast_nonneg _) _ _).symm
  calc ∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-s) = ∑ I ∈ T', f I := hsumT
    _ ≤ ∑ I ∈ (Fintype.piFinset t).image g, f I :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun I _ _ ↦ hf0 I
    _ ≤ ∑ e ∈ Fintype.piFinset t, f (g e) :=
        Finset.sum_image_le_of_nonneg fun I _ ↦ hf0 I
    _ = ∑ e ∈ Fintype.piFinset t, ∏ v : P, ((Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s)) ^ e v :=
        Finset.sum_congr rfl fun e _ ↦ hgf e
    _ = ∏ v : P, ∑ k ∈ t v, ((Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s)) ^ k :=
        (Finset.prod_univ_sum t _).symm
    _ = ∏ v ∈ P, ∑ k ∈ Finset.range (B + 1), ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) ^ k :=
        Finset.prod_coe_sort P (fun v ↦ ∑ k ∈ Finset.range (B + 1),
          ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) ^ k)
end ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
