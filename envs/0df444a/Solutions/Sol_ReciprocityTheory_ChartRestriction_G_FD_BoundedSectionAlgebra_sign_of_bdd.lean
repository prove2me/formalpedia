-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:34.06201+00:00
-- url     : https://prove2.me/submissions/dcbd03d8-c7c8-4053-9561-749e8ac3dd39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_mod_of_bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
theorem _root_.solution (h3d : ModerateCoefficientPositivity (E := E)) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (h : X.fj la ξ ν P x ≠ 0) : ∀ τ, 0 ≤ ν τ := by
  obtain ⟨C, A, hCA⟩ := mod_of_bdd X hP
  exact (h3d r X la P C A hP.1 hCA).1 ξ hξ ν x hx h
end ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
