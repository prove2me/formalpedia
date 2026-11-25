-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.keyU_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:26.859115+00:00
-- url     : https://prove2.me/submissions/05a11bf4-7fbf-412b-a93d-c8620e274f9a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (keyU (r := r) e) := by
  rintro ⟨⟨τ, a, b⟩, hi⟩ ⟨⟨τ', a', b'⟩, hj⟩ h
  simp only [keyU, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : (a : ℕ) = a' := by have := a.isLt; have := a'.isLt; omega
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  exact ⟨e.injective h3, Fin.ext ha, Fin.ext h1⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
