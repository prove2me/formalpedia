-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.tauPev_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:08.243428+00:00
-- url     : https://prove2.me/submissions/cd3c50fd-9aae-4871-88be-784fc95b9680

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
theorem _root_.solution {K : Type} [Field K] {D N : ℕ} (sg : K →+* ℂ) (pt : TVar D N → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar D N) K, q ≠ 0 → eval₂ sg pt q ≠ 0) (q : KTp K D N) :
    tauPev sg pt hpt (algebraMap (KTp K D N) (KTf K D N) q) = eval₂ sg pt q := by
  rw [tauPev, IsFractionRing.lift_algebraMap]
  rfl
end ReciprocityTheory.ChartRestriction.G.T0
