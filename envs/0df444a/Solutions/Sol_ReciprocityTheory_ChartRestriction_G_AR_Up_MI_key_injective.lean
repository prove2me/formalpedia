-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.key_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:35.087047+00:00
-- url     : https://prove2.me/submissions/865fe7c9-6e55-4859-ac3b-b81f823ad1f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (key (r := r) e) := by
  rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : a = a' := Fin.ext h2
  have hb : b = b' := Fin.ext (by omega)
  have hτ : τ = τ' := e.injective h3
  subst ha hb hτ
  rfl
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
