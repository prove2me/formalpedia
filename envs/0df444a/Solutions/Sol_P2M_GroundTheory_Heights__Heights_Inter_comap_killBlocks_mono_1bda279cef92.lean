-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_comap_killBlocks_mono_1bda279cef92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:30.510984+00:00
-- url     : https://prove2.me/submissions/500d6dbf-f71c-4383-a19b-a6cb0cefaa56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_le_comap_killBlocks_2335735e93b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_killBlocks_comp_73c8076a9a36

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {S S' : Set K}
    (h : S ⊆ S') : P.comap (killBlocks S) ≤ P.comap (killBlocks S') := by
  intro f hf
  rw [Ideal.mem_comap] at hf ⊢
  have e : killBlocks S' f = killBlocks S' (killBlocks S f) := by
    rw [← AlgHom.comp_apply, killBlocks_comp h]
  rw [e]
  exact le_comap_killBlocks hP S' hf
end GroundTheory.Heights₂.Heights.Inter
