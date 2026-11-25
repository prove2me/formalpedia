-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExG.isOpen_Om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:14.435899+00:00
-- url     : https://prove2.me/submissions/dbdb59ba-c824-4eb9-9e30-67ec5b6841f3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPf
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustGPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_isOpen_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_isOpen_dom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.FD
open scoped ContDiff
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ExG
variable {r : ℕ} (X : Data E r)
private lemma isOpen_omF (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  first
  | exact ExF.isOpen_OmF X x0
  | exact isOpen_OmF X x0
  | exact ExF.isOpen_Om X x0
  | exact (X.isOpen_dom).preimage (continuous_cpt X x0)
  | exact X.isOpen_dom.preimage (by unfold cpt; fun_prop)
  | exact X.dom_open.preimage (by unfold cpt; fun_prop)
  | exact X.hdom.preimage (by unfold cpt; fun_prop)
end ExG
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.FD
open scoped ContDiff
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.AR.Up.ExG
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExG
theorem _root_.solution (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0)) :
    IsOpen {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := by
  have hO := isOpen_omF X x0
  exact hg.continuousOn.isOpen_inter_preimage hO isOpen_ne
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExG
