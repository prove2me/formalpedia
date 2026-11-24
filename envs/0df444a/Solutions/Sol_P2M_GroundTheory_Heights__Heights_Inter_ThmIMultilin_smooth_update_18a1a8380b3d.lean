-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_smooth_update_18a1a8380b3d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:10.536855+00:00
-- url     : https://prove2.me/submissions/e78570b4-ab2d-4c77-bf4a-8bc38c3fc204

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIMultilin

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.ThmIMultilin
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIMultilin
theorem _root_.solution {n : ℕ} {L : Fin n → HermLine ι} (hL : ∀ i, IsSmoothHerm (L i)) (j : Fin n)
    {X : HermLine ι} (hX : IsSmoothHerm X) : ∀ i, IsSmoothHerm (Function.update L j X i) := by
  intro i
  by_cases h : i = j
  · subst h
    simpa using hX
  · simpa [Function.update_of_ne h] using hL i
end GroundTheory.Heights₂.Heights.Inter.ThmIMultilin
