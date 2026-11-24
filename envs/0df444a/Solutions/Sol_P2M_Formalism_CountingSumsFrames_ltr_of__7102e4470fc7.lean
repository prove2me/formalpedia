-- Prove2me | solution 1 for P2M_Formalism_CountingSumsFrames_ltr_of__7102e4470fc7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:57.88805+00:00
-- url     : https://prove2.me/submissions/c04ca00a-32d9-4d7f-b9fa-0ed53ee850f8

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : ltr fs m = m := by
  unfold ltr
  exact (Finsupp.filter_eq_self_iff _ _).mpr h
end Formalism.CountingSumsFrames
