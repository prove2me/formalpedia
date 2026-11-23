-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hsym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:52.614214+00:00
-- url     : https://prove2.me/submissions/d386e2c0-2d93-42db-8b2b-68cbe576431d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable (x : Frame X.Ψ r) (τ : X.Ψ) (e : Fin r → ℂ) (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ)
variable {x τ e}
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (u w : Fin r → ℂ) : hermC τ.1 X.Gm u w = conj (hermC τ.1 X.Gm w u) := by
  have hG : ∀ a b, τ.1 (X.Gm a b) = conj (τ.1 (X.Gm b a)) := fun a b => by
    rw [← X.Gm_herm b a, cc]
    first
      | exact NumberField.IsCMField.complexEmbedding_complexConj E _ _
      | exact (NumberField.IsCMField.complexEmbedding_complexConj E _ _).symm
      | exact NumberField.IsCMField.complexEmbedding_complexConj E _
      | exact (NumberField.IsCMField.complexEmbedding_complexConj E _).symm
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hG a b]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
