-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.addPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:04.40762+00:00
-- url     : https://prove2.me/submissions/df144685-e931-46cf-9b5a-90aacad8edff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution : (![G.add (pt k (n := 2) d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) = ![G.F] := by
  have hid : ∀ f : PS k 2 d, ev (n := 2) ![pt k d 0, pt k d 1] f = f := by
    intro f
    have hfam : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) p.1 p.2) =
        fun p => (X p : PS k 2 d) := by
      funext p
      obtain ⟨j, i⟩ := p
      fin_cases j <;> rfl
    unfold ev
    rw [hfam]
    first
    | exact congrFun MvPowerSeries.subst_self f
    | (rw [MvPowerSeries.subst_self]; rfl)
    | simp [MvPowerSeries.subst_self]
  funext j i
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  exact hid (G.F i)
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
