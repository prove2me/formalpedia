-- Prove2me | solution 1 for UnipMove.MajH.sum_splitC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:16.927816+00:00
-- url     : https://prove2.me/submissions/c73725b4-3b0d-4885-9c27-c87ba572afce

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
set_option autoImplicit false
open UnipMove UnipMove.MajH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.MajH
theorem _root_.solution (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) + ∑ m : Fin (r - X.p0), f (nI X m) := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℂ, ∀ i, g i = if h : i < r then f ⟨i, h⟩ else 0 := ⟨_, fun _ => rfl⟩
  have hr : X.p0 + (r - X.p0) = r := Nat.add_sub_cancel' X.p0_le
  have e1 : ∑ j, f j = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg, dif_pos j.isLt]
  have e2 : ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) = ∑ i ∈ Finset.range X.p0, g i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hg, dif_pos (lt_of_lt_of_le a.isLt X.p0_le)]
    rfl
  have e3 : ∑ m : Fin (r - X.p0), f (nI X m) = ∑ i ∈ Finset.range (r - X.p0), g (X.p0 + i) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hm : X.p0 + (m : ℕ) < r := by have := m.isLt; omega
    rw [hg, dif_pos hm]
    rfl
  rw [e1, e2, e3, ← Finset.sum_range_add, hr]
end UnipMove.MajH
