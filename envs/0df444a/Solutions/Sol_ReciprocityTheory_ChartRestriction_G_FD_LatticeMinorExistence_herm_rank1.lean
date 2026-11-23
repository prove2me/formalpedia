-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.herm_rank1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:25.45629+00:00
-- url     : https://prove2.me/submissions/a5c7f692-cb90-4278-b3b8-7678203e086b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
theorem _root_.solution (s : X.Ψ → ℝ) (a : X.Ψ → Fin 2 → ℂ) :
    IsHermFam (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) := by
  intro τ i k
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
