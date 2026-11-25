-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_add_sum_b89c89512e17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:54.079115+00:00
-- url     : https://prove2.me/submissions/05b8b55b-564a-4fa4-af13-988fe9a6af8d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul


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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
theorem _root_.solution {K : Type} {z : J → ℂ} (g : (J → ℂ) → ℝ) (f : K → (J → ℂ) → ℝ) (c : K → ℝ)
    (hg : ContDiffAt ℝ 2 g z) (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (w : J → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => g y + ∑ k ∈ s, c k * f k y) z ∧
      ReciprocityTheory.AnForm.levi (fun y => g y + ∑ k ∈ s, c k * f k y) z w =
        ReciprocityTheory.AnForm.levi g z w + ∑ k ∈ s, c k * ReciprocityTheory.AnForm.levi (f k) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert a s ha ih =>
    have heq : (fun y => g y + ∑ k ∈ insert a s, c k * f k y) =
        fun y => (fun y' => g y' + ∑ k ∈ s, c k * f k y') y + c a * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq, ReciprocityTheory.AnForm.levi_add_smul (c a) ih.1 (hf a) w, ih.2, Finset.sum_insert ha]
    exact ⟨ih.1.add (contDiffAt_const.mul (hf a)), by ring⟩
end GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
