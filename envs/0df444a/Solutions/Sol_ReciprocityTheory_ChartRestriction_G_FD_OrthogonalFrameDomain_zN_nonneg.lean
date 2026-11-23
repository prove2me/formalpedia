-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.zN_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:21.191461+00:00
-- url     : https://prove2.me/submissions/177534f9-7bb6-445e-9a97-213476719ae6

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
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma opN_nonneg' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ Data.opN A := by
  unfold Data.opN
  apply Real.sSup_nonneg
  rintro s ⟨v, _, rfl⟩
  positivity
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
theorem _root_.solution (Z : X.Coord) : 0 ≤ X.zN Z := by
  unfold Data.zN
  exact Real.iSup_nonneg fun τ => opN_nonneg' _
end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
