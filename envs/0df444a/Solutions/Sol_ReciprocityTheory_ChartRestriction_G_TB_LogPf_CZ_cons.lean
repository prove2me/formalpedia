-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.CZ.cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:38.812878+00:00
-- url     : https://prove2.me/submissions/f4935a6d-d6df-4e14-89d3-677fae1275e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffEv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
namespace CZ
theorem _root_.solution {m n : ℕ} {p : Pt k n d} {a : Fin m → Pt k n d} (hp : ∀ i, constantCoeff (p i) = 0) (ha : CZ a) :
    CZ (Matrix.vecCons p a) := by
  intro j
  cases j using Fin.cases with
  | zero => simpa using hp
  | succ j => simpa using ha j
end CZ
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
