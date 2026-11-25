-- Prove2me | solution 1 for PositivityTheory.KReal.graded_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:25.772288+00:00
-- url     : https://prove2.me/submissions/c2d045a1-ed1a-4c99-83c4-1fd17c61f23c

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_right
import Theorems.Thm_PI_FHS_exists_orth
import Theorems.Thm_PI_FHS_fockInner_hc_left
import Theorems.Thm_PI_FHS_fockInner_sum_right
import Theorems.Thm_PI_FockOneDegW_Core_key
import Theorems.Thm_PI_FockOneDegW_exists_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {σ : Type} [Fintype σ] (L : Submodule ℂ (MvPolynomial σ ℂ))
    (hL : ∀ d, ∀ z ∈ L, homogeneousComponent d z ∈ L) (u : MvPolynomial σ ℂ) :
    ∃ y ∈ L, ∀ z ∈ L, fockInner z (u - y) = 0 := by
  have key : ∀ d, ∀ u ∈ homog σ d, ∃ y ∈ L, ∀ z ∈ L, fockInner z (u - y) = 0 := by
    intro d u hu
    obtain ⟨y, hy, h⟩ := PI.FHS.exists_orth (L ⊓ homog σ d) d inf_le_right u
    refine ⟨y, hy.1, fun z hz => ?_⟩
    rw [← PI.FHS.fockInner_hc_left z (u - y) (Submodule.sub_mem _ hu hy.2)]
    exact h _ ⟨hL d z hz, homogeneousComponent_mem d z⟩
  choose! f hf using fun d => key d (homogeneousComponent d u) (homogeneousComponent_mem d u)
  refine ⟨∑ i ∈ Finset.range (u.totalDegree + 1), f i, Submodule.sum_mem _ fun i _ => (hf i).1, fun z hz => ?_⟩
  have e : u - ∑ i ∈ Finset.range (u.totalDegree + 1), f i =
      ∑ i ∈ Finset.range (u.totalDegree + 1), (homogeneousComponent i u - f i) := by
    rw [Finset.sum_sub_distrib, sum_homogeneousComponent]
  rw [e, PI.FHS.fockInner_sum_right]
  exact Finset.sum_eq_zero fun i _ => (hf i).2 z hz
end PositivityTheory.KReal
