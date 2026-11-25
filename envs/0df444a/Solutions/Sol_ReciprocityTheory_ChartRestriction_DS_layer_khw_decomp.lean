-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.layer_khw_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:56.518733+00:00
-- url     : https://prove2.me/submissions/dff21dc3-8105-4efc-b7ce-c9bc21d53e3f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerOrth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isKHWVec_starProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isKHWVec_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_finiteDimensional_layer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_kStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_le_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) {k : ℕ} {w : M} (hw : w ∈ layer ε E V k) {μ : Fin n → ℝ}
    (hμ : IsKHWVec ε E μ w) :
    ∃ w₀ ∈ V, IsKHWVec ε E μ w₀ ∧ ∃ ws : Fin k → M, w = w₀ + ∑ j, ws j ∧
      ∀ j : Fin k, ws j ∈ layer ε E V ((j : ℕ) + 1) ∧
        (∀ u ∈ layer ε E V (j : ℕ), inner ℂ u (ws j) = 0) ∧ IsKHWVec ε E μ (ws j) := by
  have hKU : IsKUnitary ε E := by
    intro a b hab x y
    rw [hU a b x y]
    simp [adjSign, hab]
  have key : ∀ j : ℕ, ∃ p ∈ layer ε E V j, (∀ u ∈ layer ε E V j, inner ℂ u p = inner ℂ u w) ∧
      IsKHWVec ε E μ p ∧ (w ∈ layer ε E V j → p = w) := by
    intro j
    haveI := finiteDimensional_layer (ε := ε) (E := E) hVfd j
    refine ⟨(layer ε E V j).starProjection w, Submodule.starProjection_apply_mem _ _, ?_,
      isKHWVec_starProjection hKU (layer_kStable hE hVk j) hμ, ?_⟩
    · intro u hu
      rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hu]
    · intro hw'
      exact Submodule.starProjection_eq_self_iff.mpr hw'
  choose P hP1 hP2 hP3 hP4 using key
  refine ⟨P 0, hP1 0, hP3 0, fun j => P ((j : ℕ) + 1) - P j, ?_, fun j => ⟨?_, ?_, ?_⟩⟩
  · rw [Fin.sum_univ_eq_sum_range (fun j => P (j + 1) - P j) k, Finset.sum_range_sub, hP4 k hw]
    abel
  · exact sub_mem (hP1 _) (layer_le_succ _ (hP1 _))
  · intro u hu
    rw [inner_sub_right, hP2 _ u (layer_le_succ _ hu), hP2 _ u hu, sub_self]
  · exact isKHWVec_sub (hP3 _) (hP3 _)
end ReciprocityTheory.ChartRestriction.DS
