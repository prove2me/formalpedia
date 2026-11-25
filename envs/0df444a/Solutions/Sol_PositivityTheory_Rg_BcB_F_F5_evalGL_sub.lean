-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.F5.evalGL_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:43.491797+00:00
-- url     : https://prove2.me/submissions/68d6d864-78b3-4b32-9722-dc48791fd408

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FiniteDiscreteFamilies_PeakCone
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_ShuffleChoices_EvalGLShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.F5
namespace PositivityTheory.Rg.BcB.F.F5
theorem _root_.solution {n : ℕ} (c d : (Fin n → ℤ) →₀ ℂ) (p q : ℂ) (ξ : Fin n → ℂˣ) :
    evalGL (p • c - q • d) ξ = p * evalGL c ξ - q * evalGL d ξ := by
  unfold evalGL
  rw [Finsupp.sum_sub_index (by intros; ring), Finsupp.sum_smul_index (by simp), Finsupp.sum_smul_index (by simp),
    Finsupp.mul_sum, Finsupp.mul_sum]
  simp [mul_assoc]
end PositivityTheory.Rg.BcB.F.F5
