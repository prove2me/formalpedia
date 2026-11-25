-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.bchar_kap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:58.417797+00:00
-- url     : https://prove2.me/submissions/0d6891f0-b8b6-4fa9-87e0-725e8c2b673d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_prod_low_row
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_prod_low_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
theorem _root_.solution (b : Frame X.Ψ r) (hd : ∀ τ a, b τ a a ≠ 0) :
    bchar (kapW X) b = (∏ e : Ent X, b e.1 e.2.1.1 e.2.1.1) / ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 := by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_div_distrib]
  unfold bchar
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [prod_low_row (fun a => b τ a a), prod_low_col (fun c => b τ c c), ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have ha : (a : ℕ) ≤ r - 1 := by omega
  rw [kapW, show (2 * ((a : ℕ) : ℤ) - ((r : ℤ) - 1)) = ((a : ℕ) : ℤ) - ((r - 1 - (a : ℕ) : ℕ) : ℤ) by
    push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + (a : ℕ) ≤ r)]; ring,
    zpow_sub₀ (hd τ a), zpow_natCast, zpow_natCast]
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
