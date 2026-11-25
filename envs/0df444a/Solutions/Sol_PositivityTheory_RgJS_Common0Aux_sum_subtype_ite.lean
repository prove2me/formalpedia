-- Prove2me | solution 1 for PositivityTheory.RgJS.Common0Aux.sum_subtype_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:30.015601+00:00
-- url     : https://prove2.me/submissions/4c1c74d8-6fcb-4367-87a8-34987af73720

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
theorem _root_.solution {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (f : ι → ℂ) :
    ∑ i : {i // P i}, f i = ∑ i, if P i then f i else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (univ.filter P) (by simp) f).symm
end PositivityTheory.RgJS.Common0Aux
