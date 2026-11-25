-- Prove2me | solution 1 for PI.GreenLabelSurjWork.infl_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:46.137183+00:00
-- url     : https://prove2.me/submissions/0c85ab49-cba5-44f2-90f3-6ea7d7e55427

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Theorems.Thm_PI_GreenLabelSurjWork_levi_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
namespace PI.GreenLabelSurjWork
theorem _root_.solution : infl K b lam 1 = LinearMap.id := by
  unfold infl
  simp only [levi_one, map_one]
  exact PiTensorProduct.map_id
end PI.GreenLabelSurjWork
