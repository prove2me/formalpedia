-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_L1_derivative_C_mul__8ab789f3f25e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:19:12.712612+00:00
-- url     : https://prove2.me/submissions/51c106cc-0250-469f-957b-25171a58c3ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD

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
theorem _root_.solution (c : K) (f : PowerSeries K) :
    derivative K (C c * f) = C c * derivative K f := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul]
end ReciprocityTheory.ChartRestriction.L1
