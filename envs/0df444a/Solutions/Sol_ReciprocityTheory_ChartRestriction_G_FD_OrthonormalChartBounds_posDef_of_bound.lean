-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.posDef_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:40.24449+00:00
-- url     : https://prove2.me/submissions/7ece0364-5ba5-47de-8862-7ac896ad65e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosDefOfBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_dot_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_quad_AtA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_nsq_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution {n q k : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (B : Matrix (Fin k) (Fin n) ℂ) {s : ℝ}
    (hs : s < 1) (hA : ∀ y, nsq (A.map (starRingEnd ℂ) *ᵥ y) ≤ s ^ 2 * nsq y) (hs0 : 0 ≤ s) :
    (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).PosDef := by
  have hH : (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).IsHermitian := by
    have h1 : ∀ {m : ℕ} (C : Matrix (Fin m) (Fin n) ℂ), (Cᵀ * C.map (starRingEnd ℂ)).IsHermitian := by
      intro m C
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, star_sum, mul_comm]
    exact ((Matrix.isHermitian_one.sub (h1 A)).add (h1 B))
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_sub,
    dot_self, quad_AtA, quad_AtA]
  have hpos : 0 < nsq x := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have : 0 < ‖x i‖ ^ 2 := by positivity
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i))
  have hB := nsq_nonneg (B.map (starRingEnd ℂ) *ᵥ x)
  have hA' := hA x
  have hs2 : s ^ 2 < 1 := by nlinarith
  have key : 0 < nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) := by
    nlinarith
  have : ((nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) =
      ((nsq x : ℝ) : ℂ) - ((nsq (A.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) +
        ((nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) := by push_cast; ring
  rw [← this]
  exact_mod_cast key
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
