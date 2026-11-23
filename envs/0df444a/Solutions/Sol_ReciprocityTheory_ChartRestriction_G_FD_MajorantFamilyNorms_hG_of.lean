-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hG_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:45.885434+00:00
-- url     : https://prove2.me/submissions/9871c1f4-90c7-4d15-890c-35ea79ad225a

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
theorem _root_.solution (τ : X.Ψ) : ∀ a b, τ.1 (X.Gm b a) = conj (τ.1 (X.Gm a b)) := by
  intro a b
  rw [← X.Gm_herm a b]
  first
    | simp [NumberField.IsCMField.complexEmbedding_complexConj]
    | rw [NumberField.IsCMField.complexEmbedding_complexConj]
    | simp [NumberField.IsCMField.complexConj_apply]
    | simp [NumberField.IsCMField.conj_complexEmbedding]
    | (simp only [cc]
       exact NumberField.IsCMField.complexEmbedding_complexConj ..)
end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
