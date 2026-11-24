-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.minorOn_inv_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:03:10.22287+00:00
-- url     : https://prove2.me/submissions/7cde976c-4742-47af-95ac-27dbe270b003

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unitaryGroup (Fin n) ℂ) (s : Finset (Fin n)) :
    minorOn s u⁻¹ = star (minorOn s u) := by
  have hi : u⁻¹ = star u := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hu)
  rw [hi, minorOn, minorOn, Matrix.star_eq_conjTranspose, ← conjTranspose_submatrix, det_conjTranspose]
end PositivityTheory.Rg.Sw.LVs
