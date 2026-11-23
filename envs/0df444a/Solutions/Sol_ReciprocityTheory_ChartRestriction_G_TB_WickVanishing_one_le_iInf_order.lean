-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.one_le_iInf_order
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:56.633423+00:00
-- url     : https://prove2.me/submissions/75d34ee7-3da1-4a74-a890-35513b36b4ed

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
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {τ : Type*} (a : Fin 2 × Fin d → MvPowerSeries τ k) (ha : ∀ s, constantCoeff (a s) = 0) :
    (1 : ℕ∞) ≤ ⨅ s, (a s).order := by
  refine le_iInf fun s => MvPowerSeries.le_order fun e he => ?_
  have he0 : e.degree = 0 := by
    have : e.degree < 1 := by exact_mod_cast he
    omega
  rw [Finsupp.degree_eq_zero_iff] at he0
  rw [he0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact ha s
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
