-- Prove2me | solution 1 for P2M_Formalism_CountingSumsFrames_TO_frst_of__a64a2b7f77bf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:44.365897+00:00
-- url     : https://prove2.me/submissions/928a4495-4643-41ef-8f47-229318def682

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {m : σ →₀ ℕ} (h : ∀ v, m v ≠ 0 → ¬ fs v) : frst fs m = 0 := by
  ext v
  unfold frst
  rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with hv
  · by_contra hne
    exact h v hne hv
  · rfl
end Formalism.CountingSumsFrames.TO
