-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_analyticAt_comp_symm_of_holoOn_7994d19dece0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:43.783809+00:00
-- url     : https://prove2.me/submissions/47f8f5c7-4590-4f75-8ec1-99dda7f4b5c6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_analyticAt_comp_symm_d5c087da060f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
variable {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution (hψ : IsCompatChart A ψ) {W : Set X}
    {G : X → ℂ} (hG : A.HoloOn W G) {x : X} (hxW : x ∈ W) (hx : x ∈ ψ.source) :
    AnalyticAt ℂ (G ∘ ψ.symm) (ψ x) := by
  obtain ⟨i, hi⟩ := A.cover x
  exact analyticAt_comp_symm hψ hx i hi
    (hG i (A.chart i x) ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hxW]⟩)
end GroundTheory.Heights₂.Heights.Regular
