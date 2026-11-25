-- Prove2me | solution 1 for UnipMove.MajH.en_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:26:13.789923+00:00
-- url     : https://prove2.me/submissions/a20fda2f-bbf1-4648-b1e4-1d8e3c956ea4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_nsq_mulVec_le_opN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_opN_le_zN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_opN_nonneg


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
    (a : Fin X.p0 → ℂ) : en (Matrix.of (Z τ) *ᵥ a) ≤ ρ * en a := by
  have hop : Data.opN (Matrix.of (Z τ)) ≤ ρ := (opN_le_zN X Z τ).trans hZ
  have hen : ∀ {n : ℕ} (v : Fin n → ℂ), en v = Real.sqrt (nsq v) := fun v => by
    simp [en, nsq, EuclideanSpace.norm_eq]
  rw [hen, hen]
  calc Real.sqrt (nsq (Matrix.of (Z τ) *ᵥ a)) ≤ Real.sqrt (Data.opN (Matrix.of (Z τ)) ^ 2 * nsq a) :=
        Real.sqrt_le_sqrt (nsq_mulVec_le_opN _ _)
    _ = Data.opN (Matrix.of (Z τ)) * Real.sqrt (nsq a) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (opN_nonneg _)]
    _ ≤ ρ * Real.sqrt (nsq a) := mul_le_mul_of_nonneg_right hop (Real.sqrt_nonneg _)
end UnipMove.MajH
