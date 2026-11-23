-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.ent_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:25.487634+00:00
-- url     : https://prove2.me/submissions/3270da61-510a-411a-9af5-12fa310df5fe

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
theorem _root_.solution (e e' : Ent X) :
    e = e' ↔ e.1 = e'.1 ∧ e.2.1.1 = e'.2.1.1 ∧ e.2.1.2 = e'.2.1.2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨τ, ⟨⟨a, c⟩, h⟩⟩ := e
    obtain ⟨τ', ⟨⟨a', c'⟩, h'⟩⟩ := e'
    rintro ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    subst h1 h2 h3
    rfl
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
