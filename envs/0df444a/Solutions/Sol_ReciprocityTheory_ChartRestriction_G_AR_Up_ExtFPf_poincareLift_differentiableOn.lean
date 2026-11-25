-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.poincareLift_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:38:32.03464+00:00
-- url     : https://prove2.me/submissions/c6b795b9-c284-4c9c-a668-6f5bbfff5977

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_diffOn_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bdiag_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
theorem _root_.solution (la : Wt X.Ψ r) (F : V (nd X) → ℂ) (hF : DifferentiableOn ℂ F (OmF X x0)) :
    DifferentiableOn ℂ (P0 D la F) (cell D) := by
  have hsub : ∀ x ∈ cell D, D.zOf x ∈ OmF X x0 ∧ D.bOf x ∈ Bor X.Ψ r := by
    intro x hx
    have hx' : x ∈ X.dom ∧ D.Δ x ≠ 0 := hx
    have h := D.split x hx'.1 hx'.2
    exact ⟨h.1, h.2.1⟩
  have hbc : DifferentiableOn ℂ (fun x => bchar la (D.bOf x)) (cell D) := by
    unfold bchar
    refine diffOn_prod (g := fun τ x => ∏ i, D.bOf x τ i i ^ la τ i) Finset.univ (fun τ _ => ?_)
    refine diffOn_prod (g := fun i x => D.bOf x τ i i ^ la τ i) Finset.univ (fun i _ => ?_)
    refine DifferentiableOn.zpow ?_ (Or.inl (fun x hx => FrameDegreeData.bdiag_ne (X := X) (hsub x hx).2 τ i))
    have h1 := (differentiableOn_pi.1 D.hb) τ
    have h2 := (differentiableOn_pi.1 h1) i
    exact (differentiableOn_pi.1 h2) i
  have hFz : DifferentiableOn ℂ (fun x => F (D.zOf x)) (cell D) :=
    hF.comp D.hz (fun x hx => (hsub x hx).1)
  refine (hbc.mul hFz).congr (fun x hx => ?_)
  have hx' : x ∈ X.dom ∧ D.Δ x ≠ 0 := hx
  unfold P0
  rw [if_pos hx']
  rfl
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
