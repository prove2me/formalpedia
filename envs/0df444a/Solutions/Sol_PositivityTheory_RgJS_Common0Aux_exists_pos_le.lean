-- Prove2me | solution 1 for PositivityTheory.RgJS.Common0Aux.exists_pos_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:20.907036+00:00
-- url     : https://prove2.me/submissions/1feb9bde-4b7d-4849-acc4-e603482a54ae

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_SubtypeIteSums_CommonOfLandauEuler

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.Common0Aux
variable {W X : Type} {d : X → ℕ}
namespace PositivityTheory.RgJS.Common0Aux
theorem _root_.solution {ι : Type} [Fintype ι] (f : ι → ℝ) (P : ι → Prop) (h : ∀ i, P i → 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i, P i → δ ≤ f i := by
  classical
  by_cases hs : (univ.filter P).Nonempty
  · refine ⟨min 1 ((univ.filter P).inf' hs f), lt_min one_pos ((Finset.lt_inf'_iff hs).2 fun j hj => h j ?_),
      min_le_left _ _, fun i hi => (min_le_right _ _).trans (Finset.inf'_le _ ?_)⟩
    · simpa using hj
    · simpa using hi
  · exact ⟨1, one_pos, le_rfl, fun i hi => absurd ⟨i, by simpa using hi⟩ hs⟩
end PositivityTheory.RgJS.Common0Aux
