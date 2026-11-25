-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.herm_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:42.906825+00:00
-- url     : https://prove2.me/submissions/eec99e89-41a1-4d83-949a-d6379b30e149

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
theorem _root_.solution {N : ℕ} {ω : Fin N → X.Ψ → Fin 2 → Fin 2 → ℂ} (hω : ∀ j, IsHermFam (ω j))
    (t : Fin N → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by
  intro τ i k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun j _ => by rw [hω j τ i k]
end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
