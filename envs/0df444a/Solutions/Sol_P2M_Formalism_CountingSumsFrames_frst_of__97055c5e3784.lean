-- Prove2me | solution 1 for P2M_Formalism_CountingSumsFrames_frst_of__97055c5e3784
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:20.004911+00:00
-- url     : https://prove2.me/submissions/744dc02c-70f8-408c-8888-1073c4596dbd

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
theorem _root_.solution {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : frst fs m = 0 := by
  unfold frst
  exact (Finsupp.filter_eq_zero_iff _ _).mpr fun v hv => by
    by_contra h0
    exact h v h0 hv
end Formalism.CountingSumsFrames
