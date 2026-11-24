-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_locIdeal_eq_span_6d401f7ea2c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:26.351799+00:00
-- url     : https://prove2.me/submissions/7b7709fb-6483-4c41-b66a-2f2160ddf7bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) :
    locIdeal P W y = Ideal.span {(⟨y, hy⟩ : locRing P W)} := by
  unfold locIdeal
  congr 1
  ext z
  simp only [Set.mem_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
end GroundTheory.Heights₂.Heights.Inter
