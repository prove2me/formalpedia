-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.LZ_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:46.506249+00:00
-- url     : https://prove2.me/submissions/fd2d61a0-471b-4ba8-b2df-2ba590623967

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
theorem _root_.solution {N : ℕ} {ω : Fin N → X.Ψ → Fin 2 → Fin 2 → ℂ} (hω : ∀ j, ω j ∈ X.LZ g)
    (n : Fin N → ℤ) : ∑ j, (n j : ℂ) • ω j ∈ X.LZ g := by
  have key : ∀ j, (n j : ℂ) • ω j = n j • ω j := fun j => by
    first
    | exact Int.cast_smul_eq_zsmul ℂ (n j) (ω j)
    | exact Int.cast_smul_eq_zsmul (n j) (ω j)
    | simp
  rw [Finset.sum_congr rfl fun j _ => key j]
  exact (LZsub X g).sum_mem fun j _ => (LZsub X g).zsmul_mem (hω j) (n j)
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
