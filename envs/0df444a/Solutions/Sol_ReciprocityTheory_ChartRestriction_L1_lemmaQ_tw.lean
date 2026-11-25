-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.lemmaQ_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:48:34.792112+00:00
-- url     : https://prove2.me/submissions/ebc28252-1ad9-447a-b9b7-7bf93dd3bd77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_HD_map_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_lemmaQ


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
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) {D : PowerSeries K}
    (hD : QCls l (MvPowerSeries.map ((σ.comp σ) ^ i) Φ) (PowerSeries.map ((σ.comp σ) ^ i) A) a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
        (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * PowerSeries.map ((σ.comp σ) ^ i) lam
        - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  obtain ⟨Dp, hDp, hdiv⟩ := lemmaQ hF (HD.map_sq hF h i) hD
  refine ⟨Dp, ?_, hdiv⟩
  simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
    RingHom.comp_apply]
  exact hDp
end ReciprocityTheory.ChartRestriction.L1
