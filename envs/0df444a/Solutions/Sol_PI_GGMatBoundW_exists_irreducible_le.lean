-- Prove2me | solution 1 for PI.GGMatBoundW.exists_irreducible_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:28.399549+00:00
-- url     : https://prove2.me/submissions/5cc61e9c-588d-4f35-b63a-c0da294eae7e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_RepresentationDimensionPos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_IrreducibleOfMinimal
import Theorems.Thm_PI_GGMatBoundW_irreducible_of_minimal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace PI.GGMatBoundW
theorem _root_.solution (π : Representation ℂ G V) (E : Subrepresentation π) (hE : E ≠ ⊥) :
    ∃ W : Subrepresentation π, W ≠ ⊥ ∧ W ≤ E ∧ W.toRepresentation.IsIrreducible := by
  have hex : ∃ d, ∃ W : Subrepresentation π, W ≠ ⊥ ∧ W ≤ E ∧ Module.finrank ℂ W.toSubmodule = d :=
    ⟨_, E, hE, le_rfl, rfl⟩
  obtain ⟨W, hW, hWE, hWd⟩ := Nat.find_spec hex
  refine ⟨W, hW, hWE, irreducible_of_minimal π W hW fun W' hW' hW'W => ?_⟩
  rw [hWd]
  exact Nat.find_min' hex ⟨W', hW', hW'W.trans hWE, rfl⟩
end PI.GGMatBoundW
