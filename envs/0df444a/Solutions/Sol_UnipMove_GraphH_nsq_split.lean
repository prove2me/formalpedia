-- Prove2me | solution 1 for UnipMove.GraphH.nsq_split
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T15:11:46.503274+00:00
-- url     : https://prove2.me/submissions/b32224e0-93c0-4763-919f-461f12f66173

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem UnipMove.GraphH.nsq_split (w : Fin r → ℂ) : nsq w = nsq (top X w) + nsq (bot X w) := by
  have hle := X.p0_le
  unfold nsq top bot
  simp only [nI]
  have key : ∀ f : ℕ → ℝ, (∑ i : Fin r, f i) = (∑ a : Fin X.p0, f a) + ∑ m : Fin (r - X.p0), f (X.p0 + m) := by
    intro f
    rw [Fin.sum_univ_eq_sum_range (f := f), Fin.sum_univ_eq_sum_range (f := f),
      Fin.sum_univ_eq_sum_range (f := fun m => f (X.p0 + m)), ← Finset.sum_range_add]
    rw [Nat.add_sub_cancel' hle]
  have := key (fun i => if h : i < r then ‖w ⟨i, h⟩‖ ^ 2 else 0)
  simp only [Fin.is_lt, dif_pos] at this
  rw [this]
  congr 1
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [dif_pos (by have := a.isLt; omega)]
    rfl
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [dif_pos (by have := m.isLt; omega)]

theorem solution (w : Fin r → ℂ) : nsq w = nsq (top X w) + nsq (bot X w) := by
  have hle := X.p0_le
  unfold nsq top bot
  simp only [nI]
  have key : ∀ f : ℕ → ℝ, (∑ i : Fin r, f i) = (∑ a : Fin X.p0, f a) + ∑ m : Fin (r - X.p0), f (X.p0 + m) := by
    intro f
    rw [Fin.sum_univ_eq_sum_range (f := f), Fin.sum_univ_eq_sum_range (f := f),
      Fin.sum_univ_eq_sum_range (f := fun m => f (X.p0 + m)), ← Finset.sum_range_add]
    rw [Nat.add_sub_cancel' hle]
  have := key (fun i => if h : i < r then ‖w ⟨i, h⟩‖ ^ 2 else 0)
  simp only [Fin.is_lt, dif_pos] at this
  rw [this]
  congr 1
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [dif_pos (by have := a.isLt; omega)]
    rfl
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [dif_pos (by have := m.isLt; omega)]
