-- Prove2me | solution 1 for PI.GreenLabelSurjWork.infl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:56:29.378666+00:00
-- url     : https://prove2.me/submissions/5e1cd6dd-109a-4423-a835-34e31c56f106

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_ExistsNeZeroTensor
import Theorems.Thm_PI_GreenLabelSurjWork_levi_mul

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
theorem _root_.solution (p q : parab K b) :
    infl K b lam (p * q) = infl K b lam p ∘ₗ infl K b lam q := by
  unfold infl
  rw [← PiTensorProduct.map_comp]
  congr 1
  funext c
  rw [levi_mul, map_mul]
  rfl
end PI.GreenLabelSurjWork
