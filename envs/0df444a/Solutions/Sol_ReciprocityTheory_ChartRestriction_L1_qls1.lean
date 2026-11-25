-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.qls1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:39:10.647804+00:00
-- url     : https://prove2.me/submissions/16fb5728-5962-4871-bbfa-9bdb3e65bef1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qls
import Theorems.Thm_Formalism_LT_InvIntP_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS (derivative K z)) (P Q : PowerSeries K)
    (hP0 : constantCoeff P = 0) (hQ0 : constantCoeff Q = 0)
    (hP : IntegralPS P) (hQ : IntegralPS Q) (hPQ : DivBy (l : K) (P - Q)) :
    DivBy (l : K) (z.subst P - z.subst Q) := by
  have key : ∀ (F : PowerSeries K) (d : Unit →₀ ℕ),
      MvPowerSeries.coeff d F = PowerSeries.coeff (d ()) F := by
    intro F d
    conv_lhs => rw [Finsupp.unique_single d]
    rfl
  have hP' : IntegralMv P := by
    unfold IntegralMv
    intro d
    rw [key]
    exact hP _
  have hQ' : IntegralMv Q := by
    unfold IntegralMv
    intro d
    rw [key]
    exact hQ _
  have hPQ' : DivByMv (l : K) (P - Q) := by
    unfold DivByMv
    intro d
    rw [key]
    exact hPQ _
  have h := qls hl hl1 z hz0 hz P Q hP0 hQ0 hP' hQ' hPQ'
  unfold DivBy
  intro k
  have hk := h (Finsupp.single () k)
  rwa [key, Finsupp.single_eq_same] at hk
end ReciprocityTheory.ChartRestriction.L1
