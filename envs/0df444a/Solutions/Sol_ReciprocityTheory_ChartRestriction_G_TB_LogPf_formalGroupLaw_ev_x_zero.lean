-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.formalGroupLaw_ev_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:52.776649+00:00
-- url     : https://prove2.me/submissions/568090f2-5c0d-4e2c-9ca6-8aeb66c04a7e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffEv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev


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
variable (G : FGLaw k d)
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (i : Fin d) : ev (n := 1) ![pt k d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have ha : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt _) (CZ.cons cc_zero CZ.nil)
  have hb : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) :=
    CZ.cons (cc_pt _) (CZ.cons (cc_pt _) CZ.nil)
  rw [← G.comm i, ev_ev ha hb]
  have e : (fun j l => ev (n := 1) (![pt k d 0, 0] : Fin 2 → Pt k 1 d)
      ((![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) j l)) = (![0, pt k d 0] : Fin 2 → Pt k 1 d) := by
    funext j l
    fin_cases j <;> simp [pt_apply, ev_X ha]
  rw [e]
  exact G.unit i
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
