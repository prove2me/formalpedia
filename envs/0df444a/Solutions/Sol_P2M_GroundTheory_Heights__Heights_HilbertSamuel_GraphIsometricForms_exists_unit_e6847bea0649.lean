-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_exists_unit_e6847bea0649
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:06:03.433172+00:00
-- url     : https://prove2.me/submissions/f775950c-be74-4ec5-ba0b-745d18800511

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_X_inrV_5c2a2ed5768e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_graphMap_rename_inlV_d9fcf2f5633e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_rename_mem_graphIdeal_dea023b31391
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_minor_mem_9d3fc2e3a119
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
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
theorem _root_.solution {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι} (hBP : IsBasePtFree P g)
    (j : ∀ k, ι₂ k) (a : K₂ → ℤ) {W : Ideal (MRing (Sum.elim ι ι₂))} (hW : W.IsPrime)
    (hΓW : graphIdeal P g ≤ W) (hrel : IsRelevant W) :
    ∃ u v, u ∉ W ∧ v ∉ W ∧ u * num g j a - v * den g j a ∈ graphIdeal P g := by
  have hlin : ∀ k, ∃ j', rename inlV (g ⟨k, j'⟩) ∉ W := by
    intro k
    by_contra hall
    push Not at hall
    choose i hi using fun k' => hrel (Sum.inl k')
    obtain ⟨N, hN⟩ := hBP k i
    have hle : P ⊔ Ideal.span (Set.range fun j' : ι₂ k => g ⟨k, j'⟩) ≤
        W.comap (rename (inlV (ι₂ := ι₂)) : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι₂)) :=
      sup_le (fun p hp => hΓW (rename_mem_graphIdeal g hp))
        (Ideal.span_le.mpr (Set.range_subset_iff.mpr hall))
    have hmem := hle hN
    rw [Ideal.mem_comap, map_pow, map_prod] at hmem
    obtain ⟨k', -, hk'⟩ := Ideal.IsPrime.prod_mem_iff.mp (hW.mem_of_pow_mem N hmem)
    rw [rename_X] at hk'
    exact hi k' hk'
  choose j' hj' using hlin
  have hy : ∀ k, X (inrV ⟨k, j' k⟩) ∉ W := by
    intro k hyk
    obtain ⟨j'', hj''⟩ := hrel (Sum.inr k)
    have hm := hΓW (minor_mem P g k j'' (j' k))
    have hprod : X (inrV ⟨k, j''⟩) * rename inlV (g ⟨k, j' k⟩) ∈ W := by
      have h := W.add_mem hm (W.mul_mem_right (rename inlV (g ⟨k, j''⟩)) hyk)
      rwa [sub_add_cancel] at h
    rcases hW.mem_or_mem hprod with h | h
    · exact hj'' h
    · exact hj' k h
  refine ⟨∏ k, X (inrV ⟨k, j' k⟩) ^ (a k).toNat * rename inlV (g ⟨k, j' k⟩) ^ (-a k).toNat,
    ∏ k, rename inlV (g ⟨k, j' k⟩) ^ (a k).toNat * X (inrV ⟨k, j' k⟩) ^ (-a k).toNat, ?_, ?_, ?_⟩
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
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
