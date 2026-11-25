-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices.chiOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:07.2494+00:00
-- url     : https://prove2.me/submissions/fdb0d665-abe0-4e30-add0-3c22c70b9b08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices

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
theorem _root_.solution {χ : ι → Fin 2 → Fin 2 → ℂ} (hχ : IsHermFam χ) {m : Fin N → ℝ}
    (hm : ∀ j, 2 * pr χ (ω j) = m j) : χ = chiOf ω hω hli hN m := by
  unfold chiOf
  have he : phiL ω (kap χ) = m := funext fun j => by rw [phiL_apply, th_kap hχ, hm j]
  rw [← th_kap hχ]
  congr 1
  rw [← he]
  exact ((LinearEquiv.ofBijective (phiL ω) ⟨phiL_inj ω hω hli hN, phiL_surj ω hω hli hN⟩).symm_apply_apply
    (kap χ)).symm
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
