-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.ez_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:58.368823+00:00
-- url     : https://prove2.me/submissions/391d83d3-9554-44a7-a98e-be042f23e489

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_sub


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
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
variable [Algebra ℚ k]
omit [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] h) = C (constantCoeff h) := by
  have ha : CZ (![pt k d 0, 0] : Fin 2 → Pt k 1 d) := by
    intro j i
    fin_cases j
    · show constantCoeff (X ((0 : Fin 1), i) : PS k 1 d) = 0
      first
      | exact MvPowerSeries.constantCoeff_X _
      | simp
    · show constantCoeff (0 : PS k 1 d) = 0
      exact map_zero _
  have hb : CZ (![pt k d 1] : Fin 1 → Pt k 2 d) := by
    intro j i
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show constantCoeff (X ((1 : Fin 2), i) : PS k 2 d) = 0
    first
    | exact MvPowerSeries.constantCoeff_X _
    | simp
  have hc : CZ (fun (j : Fin 0) (_ : Fin d) => (0 : PS k 1 d)) := fun j => Fin.elim0 j
  have hz : CZ (fun (_ : Fin 1) (_ : Fin d) => (0 : PS k 0 d)) := fun _ _ => map_zero _
  have hev0 : ev (fun (j : Fin 0) (_ : Fin d) => (0 : PS k 1 d)) (0 : PS k 0 d) = 0 := by
    have h0 := ev_sub hc (0 : PS k 0 d) 0
    simp only [sub_self] at h0
    exact h0
  have hfam : (fun (j : Fin 1) (i : Fin d) =>
      ev (![pt k d 0, 0] : Fin 2 → Pt k 1 d) ((![pt k d 1] : Fin 1 → Pt k 2 d) j i)) =
      fun (j : Fin 1) (i : Fin d) => ev (fun (j : Fin 0) (_ : Fin d) => (0 : PS k 1 d))
        ((fun (_ : Fin 1) (_ : Fin d) => (0 : PS k 0 d)) j i) := by
    funext j i
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show ev (![pt k d 0, 0] : Fin 2 → Pt k 1 d) (X ((1 : Fin 2), i)) =
      ev (fun (j : Fin 0) (_ : Fin d) => (0 : PS k 1 d)) (0 : PS k 0 d)
    rw [hev0, ev_X ha]
    all_goals rfl
  have hconst : ∀ g : PS k 0 d, g = C (constantCoeff g) := by
    intro g
    ext e
    have he : e = 0 := by
      first
      | exact Subsingleton.elim _ _
      | exact Finsupp.ext fun p => Fin.elim0 p.1
    subst he
    first
    | (simp; done)
    | rw [MvPowerSeries.coeff_zero_C, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [ev_ev ha hb, hfam, ← ev_ev hc hz, hconst (ev (fun (_ : Fin 1) (_ : Fin d) => (0 : PS k 0 d)) h),
    cc_ev hz, ev_C hc]
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
