-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.span_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:23.659575+00:00
-- url     : https://prove2.me/submissions/b6a571c3-83db-4641-af14-8539445c158d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientLattice_span_fixed_integral_real_parts

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
theorem _root_.solution (T : (X.Ψ → ℝ) →ₗ[ℝ] (X.Ψ → Fin 2 → Fin 2 → ℝ))
    (hT : ∀ a : E, cc a = a → IsIntegral ℤ a →
      T (fun τ => (τ.1 a).re) ∈ Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)))
    (p : X.Ψ → ℝ) : T p ∈ Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) := by
  have hp : p ∈ Submodule.span ℝ {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
      p = fun τ => (τ.1 a).re} := by
    rw [span_fixed_integral_real_parts X]
    exact Submodule.mem_top
  have hle : Submodule.span ℝ {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
      p = fun τ => (τ.1 a).re} ≤
      (Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ))).comap T := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, hi, rfl⟩
    exact hT a ha hi
  exact hle hp
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
