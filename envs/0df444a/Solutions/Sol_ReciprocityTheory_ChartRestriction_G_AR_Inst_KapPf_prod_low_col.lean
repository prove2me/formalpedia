-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.prod_low_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:23.753796+00:00
-- url     : https://prove2.me/submissions/25e76e20-b215-408c-b100-dad2ab599514

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag

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
theorem _root_.solution (g : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, g p.1.2 = ∏ c, g c ^ (r - 1 - (c : ℕ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1) (fun p => by simp)
    (fun p : Fin r × Fin r => g p.2), Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← Finset.prod_filter]
  dsimp only
  rw [Finset.prod_const]
  congr 1
  rw [← Fin.card_Ioi c]
  congr 1
  ext a
  simp
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
