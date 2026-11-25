-- Prove2me | solution 1 for P2M_GlobalTheory_FormalConnection_cc_jac__bcf9953926e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:05.413275+00:00
-- url     : https://prove2.me/submissions/0e50bc63-3c5c-48af-bea5-0383defa92c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Theorems.Thm_GlobalTheory_FormalConnection_coeff_F_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_zero_right


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.FormalLog
open GlobalTheory GlobalTheory.FormalConnection
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
namespace GlobalTheory.FormalConnection
theorem _root_.solution (c i : Fin d) : constantCoeff (Jac G c i) = if c = i then 1 else 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Jac, coeff_ev_zero_right, Finsupp.embDomain_zero, coeff_pderiv]
  simpa using coeff_F_y G c i
end GlobalTheory.FormalConnection
