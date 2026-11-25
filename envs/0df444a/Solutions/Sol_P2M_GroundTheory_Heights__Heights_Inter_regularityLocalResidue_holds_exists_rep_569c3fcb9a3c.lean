-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_exists_rep_569c3fcb9a3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:20:42.56703+00:00
-- url     : https://prove2.me/submissions/1492d89a-2be3-45d4-98c3-c75db8da6b57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_add__036135b665a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_neg__57a530bf078d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_isMultiHomog_zero__56eb92a444c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_mul_92fa4aba8533
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_one_6a94195931fa
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_one


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
open GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P : Ideal (MRing ι))
variable {P} [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
theorem _root_.solution {W : Ideal (MRing ι)} (hW : W.IsPrime) {x : FractionRing (MRing ι ⧸ P)}
    (hx : x ∈ locRing P W) :
    ∃ (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ W ∧ x * frHom P v = frHom P u := by
  have h1 : (1 : MRing ι) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, a, hv, hvW, hu, hva, rfl⟩ := hx
    exact ⟨u, v, a, hu, hva, hvW, IsLocalization.mk'_spec _ _ _⟩
  | zero => exact ⟨0, 1, 0, isMultiHomog_zero' 0, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | one => exact ⟨1, 1, 0, AvoidRing.isMultiHomog_one, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * v' + u' * v, v * v', a + a',
      isMultiHomog_add' (AvoidRing.isMultiHomog_mul hu hv') (by rw [add_comm]; exact AvoidRing.isMultiHomog_mul hu' hv),
      AvoidRing.isMultiHomog_mul hv hv', fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    rw [map_mul, map_add, map_mul, map_mul, ← e, ← e']
    ring
  | neg x _ hx =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    exact ⟨-u, v, a, isMultiHomog_neg' hu, hv, hvW, by rw [map_neg, ← e]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * u', v * v', a + a', AvoidRing.isMultiHomog_mul hu hu', AvoidRing.isMultiHomog_mul hv hv',
      fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    rw [map_mul, map_mul, ← e, ← e']
    ring
end GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
