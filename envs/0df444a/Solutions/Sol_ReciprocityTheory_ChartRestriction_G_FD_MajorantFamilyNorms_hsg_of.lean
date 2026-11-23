-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:54.060056+00:00
-- url     : https://prove2.me/submissions/6b99bccb-fd41-4054-b9be-ad91a0794a03

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantFamilyNorms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    ∀ i (h : i ≤ r), 0 < psgn X.p0 i * (gramF τ.1 X.Gm (famN (mat x τ) i h)).det.re := by
  intro i h
  unfold Data.dom GG at hx
  simp only [Set.mem_setOf_eq] at hx
  have h1 := (hx τ).2 ⟨i, Nat.lt_succ_of_le h⟩
  first
    | exact h1
    | (unfold dmin lminor gram gramF famN at h1
       exact h1)
end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
