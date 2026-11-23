-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.sac_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:40.357134+00:00
-- url     : https://prove2.me/submissions/426b0187-94a4-4fde-a07e-79bba65073aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {β : Type*} {n : ℕ} (i : Fin (n + 1)) (x : β) (p : Fin n → β) :
    Fin.succAboveCases (α := fun _ => β) i x p i = x := by
  show Fin.insertNth (α := fun _ => β) i x p i = x
  exact Fin.insertNth_apply_same _ _ _
end ReciprocityTheory.ChartRestriction.G.T0
