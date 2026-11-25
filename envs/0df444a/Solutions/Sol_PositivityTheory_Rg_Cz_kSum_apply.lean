-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.kSum_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:53.589915+00:00
-- url     : https://prove2.me/submissions/5d9e6673-933e-440e-8d16-ea157098b525

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution {N : Type} [AddCommGroup N] [Module ℝ N] {ι β : Type} (s : Finset β)
    (F : β → P [⋀^ι]→ₗ[ℝ] N) (v : ι → P) : (∑ i ∈ s, F i) v = ∑ i ∈ s, F i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]
end PositivityTheory.Rg.Cz
