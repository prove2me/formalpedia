-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hups_span_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:08:56.816872+00:00
-- url     : https://prove2.me/submissions/29972d2b-22b2-404a-9004-a235e8e2cb1d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K : Type} [Field K] (σ : K →+* ℂ) {α β : Type} [Fintype α] [Fintype β]
    {r : ℕ} (u : α → Fin r → K) (v : β → Fin r → K)
    (h : ∀ a, u a ∈ Submodule.span K (Set.range v)) (z : α → ℂ) :
    ∃ y : β → ℂ, ∀ i, ∑ a, z a * σ (u a i) = ∑ b, y b * σ (v b i) := by
  choose c hc using fun a => (Submodule.mem_span_range_iff_exists_fun K).1 (h a)
  refine ⟨fun b => ∑ a, z a * σ (c a b), fun i => ?_⟩
  have hu : ∀ a, u a i = ∑ b, c a b * v b i := fun a => by
    rw [← hc a, Finset.sum_apply]; simp [smul_eq_mul]
  simp only [hu, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
end ReciprocityTheory.ChartRestriction.G.T0
