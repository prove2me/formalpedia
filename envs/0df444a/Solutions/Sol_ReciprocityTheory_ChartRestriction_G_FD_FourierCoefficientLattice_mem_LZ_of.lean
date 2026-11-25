-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.mem_LZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:10:31.839594+00:00
-- url     : https://prove2.me/submissions/074d6f4d-7ff1-40c7-85c2-82df48a2afe8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientLattice_cc_cE

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
theorem _root_.solution (Γ : Matrix (Fin 2) (Fin 2) E) (hh : ∀ i k, cc (Γ i k) = Γ k i)
    (hi : ∀ i k, IsIntegral ℤ (Γ i k)) : X.embH (fun i k => cE g * Γ i k) ∈ X.LZ g := by
  refine ⟨fun i k => cE g * Γ i k, fun i k => ?_, fun i k => ⟨Γ i k, hi i k, rfl⟩, rfl⟩
  show cc (cE g * Γ i k) = cE g * Γ k i
  rw [show cc (cE g * Γ i k) = cc (cE g) * cc (Γ i k) from map_mul _ _ _, cc_cE, hh]
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
