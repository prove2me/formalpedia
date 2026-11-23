-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.ez_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:52.845098+00:00
-- url     : https://prove2.me/submissions/19363ab3-b584-49bd-9e53-bf6352ee4ce8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czSw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
private theorem CZ_pt_vector : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := by
  intro j i
  fin_cases j <;> simp [pt]
private theorem CZ_singleton_F : CZ (![G.F] : Fin 1 → Pt k 2 d) := by
  intro j i
  fin_cases j
  simpa using G.const i
private theorem ev_coordinate_F (i : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  rw [← G.comm i, ev_ev CZ_pt_vector czSw]
  have e : (fun j i' => ev (n := 1) ![pt k d 0, 0] ((![pt k d 1, pt k d 0] : Fin 2 → Pt k 2 d) j i')) =
      (![0, pt k d 0] : Fin 2 → Pt k 1 d) := by
    funext j i'
    fin_cases j
    · first
        | exact ev_X CZ_pt_vector 1 i'
        | simp [pt, ev_X CZ_pt_vector]
    · first
        | exact ev_X CZ_pt_vector 0 i'
        | simp [pt, ev_X CZ_pt_vector]
  rw [e, G.unit i]
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  rw [ev_ev CZ_pt_vector (CZ_singleton_F G)]
  have e : (fun j i => ev (n := 1) ![pt k d 0, 0] ((![G.F] : Fin 1 → Pt k 2 d) j i)) =
      fun j => pt k (n := 1) d j := by
    funext j i
    fin_cases j
    exact ev_coordinate_F G i
  rw [e, ev_pt]
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
