-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.per_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:47:52.385378+00:00
-- url     : https://prove2.me/submissions/e780068a-c039-488d-8e36-4e15a2a02785

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_spanBn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (X : PT E) (n : ℕ) {F : Type} (g : (Fin n → Vsp X.dim) → F)
    (hper : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → ∀ v, g (v + γ) = g v) :
    ∀ (γ : (Submodule.span ℤ (Set.range (Bn X n))).toAddSubgroup) (x), g (γ +ᵥ x) = g x := by
  intro γ x
  have h1 : γ +ᵥ x = x + (γ : Fin n → Vsp X.dim) := add_comm _ _
  rw [h1]
  exact hper _ ((mem_spanBn X n _).mp γ.2) x
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
