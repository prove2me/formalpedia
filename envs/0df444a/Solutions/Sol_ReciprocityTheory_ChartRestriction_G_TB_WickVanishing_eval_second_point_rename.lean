-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eval_second_point_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:51.213775+00:00
-- url     : https://prove2.me/submissions/92f2eb22-7a1a-4339-9b88-0e1c6c171b79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (φ : PS k 1 d) : ev (n := 2) ![pt k d 1] φ = rename (eZ d) φ := by
  rw [rename_eq_subst]
  unfold ev
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
