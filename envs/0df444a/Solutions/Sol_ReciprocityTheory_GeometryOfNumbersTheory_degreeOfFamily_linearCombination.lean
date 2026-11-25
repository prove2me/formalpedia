-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily_linearCombination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:43:18.981115+00:00
-- url     : https://prove2.me/submissions/2454a9a5-6919-4407-bad3-f73c269b3827

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_ds_relIndex_span_comb
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_ds_det_ne_zero_of_comb
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_log_gram_comb
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_ds_sum_log_normSq_embeddings


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (h : HermFam K V) (E : Submodule (𝓞 K) V) {r : ℕ} {v : Fin r → V}
    (hv : LinearIndependent K v) (g : Matrix (Fin r) (Fin r) (𝓞 K))
    (hv' : LinearIndependent K (fun j => ∑ i, g i j • v i))
    (hvE : Submodule.span (𝓞 K) (Set.range v) ≤ E)
    (hne : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0) :
    degreeOfFamily h E (fun j => ∑ i, g i j • v i) = degreeOfFamily h E v := by
  classical
  have hg := ds_det_ne_zero_of_comb g hv'
  have hle : Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i) ≤
      Submodule.span (𝓞 K) (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hle)
    ((Submodule.toAddSubgroup_le _ _).2 hvE)
  rw [ds_relIndex_span_comb hv g hg] at hmul
  have hconv : (fun j => ∑ i, g i j • v i) =
      fun j => ∑ i, (g.map (algebraMap (𝓞 K) K)) i j • v i := by
    funext j
    simp only [Matrix.map_apply, algebraMap_smul]
  have hdetmap : algebraMap (𝓞 K) K g.det = (g.map (algebraMap (𝓞 K) K)).det :=
    RingHom.map_det (algebraMap (𝓞 K) K) g
  have hGdet : (g.map (algebraMap (𝓞 K) K)).det ≠ 0 := by
    rw [← hdetmap]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hg
  have hsum : ∑ σ : K →+* ℂ, Real.log (h.gram σ (fun j => ∑ i, g i j • v i)).det.re =
      2 * Real.log |(Algebra.norm ℚ (g.map (algebraMap (𝓞 K) K)).det : ℝ)| +
        ∑ σ : K →+* ℂ, Real.log (h.gram σ v).det.re := by
    rw [hconv, ← ds_sum_log_normSq_embeddings _ hGdet, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => h.ds_log_gram_comb σ hv _ hGdet
  have hnorm : (Algebra.norm ℚ (g.map (algebraMap (𝓞 K) K)).det : ℝ) =
      ((Algebra.norm ℤ g.det : ℤ) : ℝ) := by
    rw [← hdetmap]
    have h1 := Algebra.coe_norm_int g.det
    have h2 : ((Algebra.norm ℚ (algebraMap (𝓞 K) K g.det) : ℚ) : ℝ) =
        (((Algebra.norm ℤ g.det : ℤ) : ℚ) : ℝ) := by
      rw [h1]
    rw [h2]
    push_cast
    rfl
  have hne1 : (((Algebra.norm ℤ g.det).natAbs : ℕ) : ℝ) ≠ 0 := by
    have : Algebra.norm ℤ g.det ≠ 0 := Algebra.norm_ne_zero_iff.2 hg
    exact_mod_cast Int.natAbs_ne_zero.2 this
  have hne2 : (((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℕ) : ℝ)
      ≠ 0 := by exact_mod_cast hne
  unfold degreeOfFamily
  rw [← hmul, Nat.cast_mul, Real.log_mul hne1 hne2, hsum, hnorm, Nat.cast_natAbs, Int.cast_abs]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
