-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_component_mem_ker_08c85875dfc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:05.011594+00:00
-- url     : https://prove2.me/submissions/2bc40216-c1ea-4127-8f45-c037f26b369e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrdOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrderOne_isWeightedHomogeneous_multiConeMap_4a037a706f8f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOrderOne
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOrderOne
theorem _root_.solution (c : (Σ k, ι k) → Φ) {f : MRing ι} (hf : f ∈ RingHom.ker (T.multiConeMap c))
    (m : K → ℕ) :
    weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) m f ∈
      RingHom.ker (T.multiConeMap c) := by
  rw [RingHom.mem_ker] at hf ⊢
  have hsum := congrArg (weightedHomogeneousComponent (fun k : K => (Pi.single k 1 : K → ℕ)) m) hf
  rw [← sum_weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum, map_sum, map_zero] at hsum
  rw [← (isWeightedHomogeneous_multiConeMap c
    (weightedHomogeneousComponent_isWeightedHomogeneous m f)).weightedHomogeneousComponent_same, ← hsum]
  by_cases hm : weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) m f = 0
  · rw [hm, map_zero, map_zero]
    symm
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b = m
    · rw [hb, hm, map_zero, map_zero]
    · exact (isWeightedHomogeneous_multiConeMap c
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne m (Ne.symm hb)
  · rw [Finset.sum_eq_single m]
    · intro b _ hb
      exact (isWeightedHomogeneous_multiConeMap c
        (weightedHomogeneousComponent_isWeightedHomogeneous b f)).weightedHomogeneousComponent_ne m (Ne.symm hb)
    · intro h
      exact absurd ((Set.Finite.mem_toFinset _).2 hm) h
end GroundTheory.Heights₂.Heights.Inter.DiagonalOrderOne
