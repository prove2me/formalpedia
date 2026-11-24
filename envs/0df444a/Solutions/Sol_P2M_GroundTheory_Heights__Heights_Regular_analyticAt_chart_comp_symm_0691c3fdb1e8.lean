-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_analyticAt_chart_comp_symm_0691c3fdb1e8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:34.183571+00:00
-- url     : https://prove2.me/submissions/4f0003f3-473f-4508-aca6-7d5e8f063be6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts

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
theorem _root_.solution (hψ : IsCompatChart A ψ) {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) : AnalyticAt ℂ (A.chart i ∘ ψ.symm) (ψ x) :=
  (hψ i).2 (ψ x) ⟨ψ.map_source hx, by simp [ψ.left_inv hx, hxi]⟩
end GroundTheory.Heights₂.Heights.Regular
