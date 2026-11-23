-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.sac_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:08.274803+00:00
-- url     : https://prove2.me/submissions/b81c3557-c92e-49ef-b650-61692d2da80b

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
theorem _root_.solution {β : Type*} {n : ℕ} (i : Fin (n + 1)) (x : β) (p : Fin n → β) (k : Fin n) :
    Fin.succAboveCases (α := fun _ => β) i x p (i.succAbove k) = p k := by
  show Fin.insertNth (α := fun _ => β) i x p (i.succAbove k) = p k
  exact Fin.insertNth_apply_succAbove _ _ _ _
end ReciprocityTheory.ChartRestriction.G.T0
