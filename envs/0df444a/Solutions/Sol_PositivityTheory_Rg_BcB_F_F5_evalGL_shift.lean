-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.F5.evalGL_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:41.045668+00:00
-- url     : https://prove2.me/submissions/c8015620-8807-4c35-9493-178ee5a9d425

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
theorem _root_.solution {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (y : Fin n → ℤ) (ξ : Fin n → ℂˣ) :
    evalGL (c.mapDomain (· + y)) ξ = ((∏ i, ξ i ^ y i : ℂˣ) : ℂ) * evalGL c ξ := by
  unfold evalGL
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
  ring
end PositivityTheory.Rg.BcB.F.F5
