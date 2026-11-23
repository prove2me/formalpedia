-- Prove2me | solution 1 for PI.PoincareSeriesInner.W.poinc_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:35.054348+00:00
-- url     : https://prove2.me/submissions/309bfd59-4b0a-4012-a9b4-95b0866f0e06

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_CplxDC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldDCUnfold
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_ComplexDoubleCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
open PI PI.PoincareSeriesInner PI.PoincareSeriesInner.W
universe u
namespace PI.PoincareSeriesInner.W
theorem _root_.solution {G : Type*} [Group G] (E : Set G) (v : Fin 4 → G → ℝ≥0∞) (f : G → ℂ)
    (hf : ∀ x, f x = ∑ k, cf k * ((v k x).toReal : ℂ))
    (hv : ∀ k x, ∑' δ : E, v k ((δ : G) * x) ≠ ⊤) (x : G) :
    poinc E f x = ∑ k, cf k * (((∑' δ : E, v k ((δ : G) * x))).toReal : ℂ) := by
  have hsum : ∀ k, Summable (fun δ : E => ((v k ((δ : G) * x)).toReal : ℂ)) :=
    fun k => Complex.summable_ofReal.2 (ENNReal.summable_toReal (hv k x))
  unfold poinc
  simp_rw [hf]
  rw [Summable.tsum_finsetSum (fun k _ => (hsum k).mul_left (cf k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left, ← Complex.ofReal_tsum, ENNReal.tsum_toReal_eq (fun δ => ENNReal.ne_top_of_tsum_ne_top (hv k x) δ)]
end PI.PoincareSeriesInner.W
