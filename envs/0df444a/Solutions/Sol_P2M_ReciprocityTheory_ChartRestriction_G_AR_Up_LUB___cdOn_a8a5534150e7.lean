-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___cdOn_a8a5534150e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:15:22.215893+00:00
-- url     : https://prove2.me/submissions/3115a165-a870-4006-af97-75261a7c242c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB_isOpen_Uc
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB___diffOn_a7027ba2f598
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
theorem _root_.solution : ContDiffOn ℂ ∞ (Φ X b1 D) (Uc X b1 D) := by
  refine contDiffOn_piLp' 2 fun i => ?_
  have hi : DifferentiableOn ℂ (fun x => (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i) (Φ X b1 D x))
      (Uc X b1 D) :=
    (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i).differentiable.comp_differentiableOn (Φ_diffOn X b1 D)
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn (nd X) _ _ (isOpen_Uc X b1 D) hi
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
