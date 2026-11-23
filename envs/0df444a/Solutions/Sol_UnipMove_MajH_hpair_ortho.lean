-- Prove2me | solution 1 for UnipMove.MajH.hpair_ortho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:11.004318+00:00
-- url     : https://prove2.me/submissions/043b90de-3ff4-40ef-b2fe-b174afcbc695

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UnipMove.MajH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma sum_three_rotate {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (T : α → β → γ → M) :
    ∑ i, ∑ j, ∑ b, T i j b = ∑ b, ∑ i, ∑ j, T i j b :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
end Frames
end
end UnipMove.MajH
namespace UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
end UnipMove
end

set_option autoImplicit false
open UnipMove UnipMove.MajH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.MajH
theorem _root_.solution {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (c : Fin r → ℂ) (b : Fin r) :
    hermC τ.1 X.Gm (mat x τ *ᵥ c) (col (mat x τ) b) = c b * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) := by
  have hg : ∀ a, (∑ i, ∑ j, mat x τ i a * τ.1 (X.Gm i j) * conj (mat x τ j b)) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
    intro a
    have := congrFun (congrFun (ho τ) a) b
    simpa [gram, hermC, col, Matrix.diagonal_apply] using this
  simp only [hermC, Matrix.mulVec, dotProduct, col, Finset.sum_mul]
  rw [sum_three_rotate]
  have e : ∀ a, (∑ i, ∑ j, mat x τ i a * c a * τ.1 (X.Gm i j) * conj (mat x τ j b)) =
      c a * (if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0) := by
    intro a
    rw [← hg a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end UnipMove.MajH
