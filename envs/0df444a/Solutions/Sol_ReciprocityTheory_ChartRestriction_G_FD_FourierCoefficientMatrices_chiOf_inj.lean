-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices.chiOf_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:16.090313+00:00
-- url     : https://prove2.me/submissions/1af8035b-e11b-40cf-827a-b1a280ad1451

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_chiOf_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)
variable (hω : ∀ j, IsHermFam (ω j)) (hli : LinearIndependent ℝ ω) (hN : N = 4 * Fintype.card ι)
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
theorem _root_.solution : Function.Injective (chiOf ω hω hli hN) := by
  intro m m' h
  funext j
  rw [← chiOf_pair ω hω hli hN m j, ← chiOf_pair ω hω hli hN m' j, h]
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
