-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.xZ_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:52:51.107418+00:00
-- url     : https://prove2.me/submissions/2e9abe3b-a4b0-4082-93b5-20af14eec171

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LogDOfPosBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
theorem _root_.solution (x : Frame X.Ψ r) : Differentiable ℂ fun Z : X.Coord => X.xZ x Z := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  have hL : ∀ j, Differentiable ℂ fun Z : X.Coord => X.lowBlock Z τ j b := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  show Differentiable ℂ fun Z : X.Coord => ∑ j, mat x τ a j * X.lowBlock Z τ j b
  first
    | exact Differentiable.fun_sum (fun j _ => (hL j).const_mul _)
    | exact Differentiable.sum (fun j _ => (hL j).const_mul _)
end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
