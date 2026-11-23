-- Prove2me | solution 1 for PI.GreenLabelSurjWork.simple_of_irr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:49.122872+00:00
-- url     : https://prove2.me/submissions/8104849f-3abd-4b9d-b57d-1b12b4a68605

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Simple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {G : Type} [Group G] [Fintype G]
namespace PI.GreenLabelSurjWork
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [σ.IsIrreducible] : Simple (FDRep.of σ) := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  rw [FDRep.simple_iff_end_is_rank_one]
  rw [← (FDRep.forget₂HomLinearEquiv _ _).finrank_eq, (repHomLin _ _).finrank_eq]
  exact Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := σ)
end PI.GreenLabelSurjWork
