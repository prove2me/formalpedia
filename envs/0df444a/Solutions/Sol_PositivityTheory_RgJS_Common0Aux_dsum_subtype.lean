-- Prove2me | solution 1 for PositivityTheory.RgJS.Common0Aux.dsum_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:08.160394+00:00
-- url     : https://prove2.me/submissions/180eccb8-7f20-477a-a839-df8559fb2cfd

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_SubtypeIteSums_CommonOfLandauEuler
import Theorems.Thm_PositivityTheory_RgJS_Common0Aux_sum_subtype_ite

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
theorem _root_.solution {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (f : ι → ι → ℂ) :
    ∑ i : {i // P i}, ∑ j : {i // P i}, f i j = ∑ i, ∑ j, if P i ∧ P j then f i j else 0 := by
  rw [sum_subtype_ite P (fun i => ∑ j : {i // P i}, f i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : P i
  · simp [hi, sum_subtype_ite P (fun j => f i j)]
  · simp [hi]
end PositivityTheory.RgJS.Common0Aux
