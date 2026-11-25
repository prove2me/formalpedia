-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices.Neg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:57:20.170739+00:00
-- url     : https://prove2.me/submissions/8f10c1d6-636f-43b9-8ebc-a6aa489ff960

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowerBlockMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma hermC_sum_smul_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ}
    (c : Fin m → ℂ) (y : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ b, c b • y b) v = ∑ b, c b * hermC τ G (y b) v := by
  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b' _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
end
end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
theorem _root_.solution (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    Neg X x0 τ (∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) =
      ∑ a, ‖(Bmat X h1 z0 x0 τ *ᵥ u) a‖ ^ 2 := by
  unfold PositiveSpanMatrices.Neg
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have h : (Bmat X h1 z0 x0 τ *ᵥ u) a = -∑ b, u b * hermC τ.1 X.Gm
      (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) (col (mat x0 τ) (kap X.p0_le a)) := by
    simp only [Matrix.mulVec, dotProduct, Bmat, Matrix.of_apply, neg_mul, Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
  rw [hermC_sum_smul_left', h, norm_neg]
end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
