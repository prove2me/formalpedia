-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.ez_dx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:55:55.422671+00:00
-- url     : https://prove2.me/submissions/e48d9264-fb1e-4366-b632-0a4e592a64d3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czSw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev

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
theorem _root_.solution (j a : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) (G.F j)) = if j = a then 1 else 0 := by
  have h := congrArg (pderiv k ((0 : Fin 1), a)) (ev_coordinate_F G j)
  rw [pderiv_ev CZ_pt_vector, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pt, MvPowerSeries.pderiv_X, Pi.single_apply] at h
  first
    | exact h
    | simpa [eq_comm] using h
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
