-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:56:28.520842+00:00
-- url     : https://prove2.me/submissions/fe917413-3a6f-4147-91f2-1cff09bd6a09

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_formalFamilyConstantCoeffZero_zero_secondVar
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev


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
theorem _root_.solution (i b : Fin d) : constantCoeff (Jac G i b) = if i = b then 1 else 0 := by
  have hE : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := by
    intro j i
    fin_cases j <;> simp [pt]
  have h := congrArg (pderiv k ((0 : Fin 1), b)) (G.unit i)
  rw [pderiv_ev formalFamilyConstantCoeffZero_zero_secondVar, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pt, MvPowerSeries.pderiv_X, Pi.single_apply] at h
  have h2 := congrArg constantCoeff h
  rw [cc_ev formalFamilyConstantCoeffZero_zero_secondVar] at h2
  show constantCoeff (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F i))) = _
  rw [cc_ev hE, h2]
  by_cases hib : i = b
  · subst hib
    simp
  · simp [hib, Ne.symm hib]
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
