-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_845b98ac4443
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:41.509119+00:00
-- url     : https://prove2.me/submissions/de220f20-fbc1-46a3-ab97-769e03a4406c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_comp_symm_eventuallyEq_0d3f4d850af4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_analyticAt_chart_comp_symm_0691c3fdb1e8

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
theorem _root_.solution (hψ : IsCompatChart A ψ) {n : WithTop ℕ∞} {g : X → ℝ} {x : X}
    (hx : x ∈ ψ.source) (i : Fin A.n) (hxi : x ∈ (A.chart i).source)
    (hg : ContDiffAt ℝ n (g ∘ (A.chart i).symm) (A.chart i x)) :
    ContDiffAt ℝ n (g ∘ ψ.symm) (ψ x) := by
  have hτ := (analyticAt_chart_comp_symm hψ hx i hxi).restrictScalars (𝕜 := ℝ)
  have hg' : ContDiffAt ℝ n (g ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (ψ x)) := by
    simpa [ψ.left_inv hx] using hg
  exact (hg'.comp (ψ x) hτ.contDiffAt).congr_of_eventuallyEq
    (comp_symm_eventuallyEq g hx i hxi).symm
end GroundTheory.Heights₂.Heights.Regular
