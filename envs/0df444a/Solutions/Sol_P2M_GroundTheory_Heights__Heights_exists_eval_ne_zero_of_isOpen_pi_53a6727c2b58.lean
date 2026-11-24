-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_eval_ne_zero_of_isOpen_pi_53a6727c2b58
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:48.735991+00:00
-- url     : https://prove2.me/submissions/3c4d91b2-be7c-4138-8942-d078d81b0817

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAwayZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {σ : Type*} [Finite σ] {F : MvPolynomial σ ℂ} (hF : F ≠ 0)
    {S : Set (σ → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y F ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hF
  have hinf : ∀ i, (u i).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) ((hu i).1.mem_nhds (hu i).2)
  refine (funext_set_iff (p := F) (q := 0) u hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hsub hy)
end GroundTheory.Heights₂.Heights
