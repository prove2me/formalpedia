-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.mjg_pb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:52:51.816202+00:00
-- url     : https://prove2.me/submissions/913a1126-f473-4e54-972d-f8424833e8d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates

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
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (δ : Fin X.p0 → ℂ) :
    mjpb X (mjg X Z τ δ) = Matrix.of (Z τ) *ᵥ δ := by
  funext m
  simp only [mjpb, mjg, nI, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, Data.lowBlock, Matrix.of_apply,
    Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hne : ¬ ((⟨X.p0 + (m : ℕ), by have := m.isLt; have := X.p0_le; omega⟩ : Fin r) =
      Fin.castLE X.p0_le c) := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hlt : X.p0 ≤ X.p0 + (m : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 := ⟨by omega, by simp⟩
  rw [if_neg hne, dif_pos hlt, zero_add, mul_comm]
  congr 2 <;> ext <;> simp
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
