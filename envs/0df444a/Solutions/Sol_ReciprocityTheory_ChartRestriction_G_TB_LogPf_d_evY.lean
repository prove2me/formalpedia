-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.d_evY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:05.158721+00:00
-- url     : https://prove2.me/submissions/42b4bff0-7926-424d-b681-d9db4b9c5b9b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
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
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (h : PS k 1 d) (b : Fin d) :
    pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 1] h) = ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), b) h) := by
  have hXd : ∀ v w : Fin 2 × Fin d, pderiv k v (X w : PS k 2 d) = if v = w then 1 else 0 := by
    intro v w
    first
    | (simp [MvPowerSeries.pderiv_X, Pi.single_apply]; done)
    | (by_cases hvw : v = w <;> simp [hvw, MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne]; done)
    | (by_cases hvw : v = w <;> simp [hvw, MvPowerSeries.pderiv_X]; done)
    | (by_cases hvw : v = w
       · subst hvw
         simp
       · simp [hvw])
  have hcz : CZ (![pt k d 1] : Fin 1 → Pt k 2 d) := by
    intro j i
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show constantCoeff (X ((1 : Fin 2), i) : PS k 2 d) = 0
    first
    | exact MvPowerSeries.constantCoeff_X _
    | simp
  rw [pderiv_ev hcz, Fintype.sum_eq_single ((0 : Fin 1), b)]
  · show ev _ (pderiv k ((0 : Fin 1), b) h) * pderiv k ((1 : Fin 2), b) (X ((1 : Fin 2), b)) = _
    rw [hXd, if_pos rfl, mul_one]
  · rintro ⟨j, i⟩ hne
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show ev _ _ * pderiv k ((1 : Fin 2), b) (X ((1 : Fin 2), i)) = 0
    rw [hXd, if_neg, mul_zero]
    intro heq
    apply hne
    rw [(Prod.mk.inj heq).2]
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
