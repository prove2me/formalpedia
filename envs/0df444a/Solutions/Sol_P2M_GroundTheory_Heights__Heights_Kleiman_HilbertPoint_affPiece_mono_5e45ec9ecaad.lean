-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_mono_5e45ec9ecaad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:34:38.32692+00:00
-- url     : https://prove2.me/submissions/e3693ff3-a8d1-4097-9ea3-df1d6c9fad74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
theorem _root_.solution (hj : y j ≠ 0) {m n : ℕ} (h : m ≤ n) :
    affPiece k y j m ≤ affPiece k y j n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  refine Submodule.subset_span ⟨X j ^ (n - m) * f, ?_, ?_⟩
  · have := (isHomogeneous_X_pow (R := k) j (n - m)).mul hf
    rwa [Nat.sub_add_cancel h] at this
  · simp [aff, hj]
end GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
