-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_exists_unit_e7832c878c51
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:19.321701+00:00
-- url     : https://prove2.me/submissions/748f26d9-8d8c-492c-9bb3-e717db765c5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_X_inrV_c69762fa971f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_rename_inlV_833d0140fb95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_minor_mem_663e0dfb408f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
theorem _root_.solution {P : Ideal (MRing ι)} {A : ∀ k, ι₂ k → ι k → ℤ} (hBP : IsBasePtFree P (linForm A))
    (j : ∀ k, ι₂ k) (a : K → ℤ) {W : Ideal (MRing (Sum.elim ι ι₂))} (hW : W.IsPrime)
    (hΓW : graphIdeal P (linForm A) ≤ W) (hrel : IsRelevant W) :
    ∃ u v, u ∉ W ∧ v ∉ W ∧ u * num A j a - v * den A j a ∈ graphIdeal P (linForm A) := by
  have := hW
  have hlin : ∀ k, ∃ j', rename inlV (linForm A ⟨k, j'⟩) ∉ W := by
    intro k
    by_contra hall
    push Not at hall
    choose i hi using fun k' => hrel (Sum.inl k')
    obtain ⟨N, hN⟩ := hBP k i
    have hle : P ⊔ Ideal.span (Set.range fun j' : ι₂ k => linForm A ⟨k, j'⟩) ≤
        W.comap (rename (inlV (ι₂ := ι₂)) : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι₂)) := by
      refine sup_le (fun p hp => hΓW ?_) (Ideal.span_le.mpr (Set.range_subset_iff.mpr hall))
      rw [graphIdeal, RingHom.mem_ker, graphMap_rename_inlV, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    have hmem := hle hN
    rw [Ideal.mem_comap, map_pow, map_prod] at hmem
    obtain ⟨k', -, hk'⟩ := Ideal.IsPrime.prod_mem_iff.mp (hW.mem_of_pow_mem N hmem)
    rw [rename_X] at hk'
    exact hi k' hk'
  choose j' hj' using hlin
  have hy : ∀ k, X (inrV ⟨k, j' k⟩) ∉ W := by
    intro k hyk
    obtain ⟨j'', hj''⟩ := hrel (Sum.inr k)
    have hm := hΓW (minor_mem P A k j'' (j' k))
    have hprod : X (inrV ⟨k, j''⟩) * rename inlV (linForm A ⟨k, j' k⟩) ∈ W := by
      have h := W.add_mem hm (W.mul_mem_right (rename inlV (linForm A ⟨k, j''⟩)) hyk)
      rwa [sub_add_cancel] at h
    rcases hW.mem_or_mem hprod with h | h
    · exact hj'' h
    · exact hj' k h
  refine ⟨∏ k, X (inrV ⟨k, j' k⟩) ^ (a k).toNat * rename inlV (linForm A ⟨k, j' k⟩) ^ (-a k).toNat,
    ∏ k, rename inlV (linForm A ⟨k, j' k⟩) ^ (a k).toNat * X (inrV ⟨k, j' k⟩) ^ (-a k).toNat, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    rcases hW.mem_or_mem hk with h | h
    · exact hy k (hW.mem_of_pow_mem _ h)
    · exact hj' k (hW.mem_of_pow_mem _ h)
  · intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    rcases hW.mem_or_mem hk with h | h
    · exact hj' k (hW.mem_of_pow_mem _ h)
    · exact hy k (hW.mem_of_pow_mem _ h)
  · rw [graphIdeal, RingHom.mem_ker, map_sub, sub_eq_zero]
    simp only [num, den, map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
