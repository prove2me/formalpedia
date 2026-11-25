-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.HD.map_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:02.684831+00:00
-- url     : https://prove2.me/submissions/e8c047b8-48d3-4abe-8b07-5e35c3307a8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_HD_map_frobenius_sq

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
namespace HD
theorem _root_.solution (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) :
    HD σ (PowerSeries.map ((σ.comp σ) ^ i) lam) (MvPowerSeries.map ((σ.comp σ) ^ i) Φ)
      (PowerSeries.map ((σ.comp σ) ^ i) A) a := by
  induction i with
  | zero =>
    simp only [pow_zero, RingHom.one_def, MvPowerSeries.map_id, PowerSeries.map_id, RingHom.id_apply]
    exact h
  | succ i ih =>
    have h1 := HD.map_frobenius_sq hF ih
    simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
      RingHom.comp_apply]
    exact h1
end HD
end ReciprocityTheory.ChartRestriction.L1
