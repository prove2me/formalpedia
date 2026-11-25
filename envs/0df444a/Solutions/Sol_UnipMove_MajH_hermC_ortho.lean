-- Prove2me | solution 1 for UnipMove.MajH.hermC_ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:40:49.604807+00:00
-- url     : https://prove2.me/submissions/42cc6821-3d22-43bf-b799-06b7895142e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
import Theorems.Thm_UnipMove_MajH_sum_splitC
import Theorems.Thm_UnipMove_MajH_hpair_ortho
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
theorem _root_.solution {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (mat x τ *ᵥ u) (mat x τ *ᵥ w) =
      dot (top X u) (top X w) - dot (bot X u) (bot X w) := by
  have hlin : ∀ U : Fin r → ℂ, hermC τ.1 X.Gm U (mat x τ *ᵥ w) =
      ∑ b, conj (w b) * hermC τ.1 X.Gm U (col (mat x τ) b) := by
    intro U
    simp only [hermC, col, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    rw [sum_three_rotate]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring
  have hn : ∀ m : Fin (r - X.p0), ((nI X m : Fin r) : ℕ) = X.p0 + m := fun m => rfl
  have hs1 : ∀ a : Fin X.p0, sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 :=
    fun a => by simp [sgn, a.isLt]
  have hs2 : ∀ m : Fin (r - X.p0), sgn X.p0 ((nI X m : Fin r) : ℕ) = -1 :=
    fun m => by simp [sgn, hn]
  rw [hlin]
  simp only [hpair_ortho X ho τ u]
  rw [sum_splitC X]
  simp only [hs1, hs2, dot, top, bot]
  push_cast
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;> ring
end UnipMove.MajH
