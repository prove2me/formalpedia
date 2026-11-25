-- Prove2me | solution 1 for UnipMove.MajH.en_adj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:08.937731+00:00
-- url     : https://prove2.me/submissions/8698e189-78cf-49c2-b175-210f584c5b4a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
import Theorems.Thm_UnipMove_MajH_re_dot_self
import Theorems.Thm_UnipMove_MajH_dot_adj
import Theorems.Thm_UnipMove_MajH_norm_dot_le
import Theorems.Thm_UnipMove_MajH_en_mulVec_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.MajH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.MajH
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hZ : X.zN Z ≤ ρ)
    (b : Fin (r - X.p0) → ℂ) : en ((Matrix.of (Z τ))ᴴ *ᵥ b) ≤ ρ * en b := by
  have hen : ∀ {n : ℕ} (v : Fin n → ℂ), en v = Real.sqrt (nsq v) := fun v => by
    simp [en, nsq, EuclideanSpace.norm_eq]
  have hsq : en ((Matrix.of (Z τ))ᴴ *ᵥ b) ^ 2 = nsq ((Matrix.of (Z τ))ᴴ *ᵥ b) := by
    rw [hen, Real.sq_sqrt]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : nsq ((Matrix.of (Z τ))ᴴ *ᵥ b) ≤
      en b * (ρ * en ((Matrix.of (Z τ))ᴴ *ᵥ b)) := by
    rw [← re_dot_self, dot_adj, Matrix.conjTranspose_conjTranspose]
    calc (dot b (Matrix.of (Z τ) *ᵥ ((Matrix.of (Z τ))ᴴ *ᵥ b))).re
        ≤ ‖dot b (Matrix.of (Z τ) *ᵥ ((Matrix.of (Z τ))ᴴ *ᵥ b))‖ := Complex.re_le_norm _
      _ ≤ en b * en (Matrix.of (Z τ) *ᵥ ((Matrix.of (Z τ))ᴴ *ᵥ b)) := norm_dot_le _ _
      _ ≤ en b * (ρ * en ((Matrix.of (Z τ))ᴴ *ᵥ b)) :=
        mul_le_mul_of_nonneg_left (en_mulVec_le X Z τ hρ hZ _) (norm_nonneg _)
  have hy0 : 0 ≤ en ((Matrix.of (Z τ))ᴴ *ᵥ b) := norm_nonneg _
  have hb0 : 0 ≤ en b := norm_nonneg _
  rcases hy0.eq_or_lt with h | h
  · rw [← h]
    positivity
  · exact le_of_mul_le_mul_right (by nlinarith) h
end UnipMove.MajH
