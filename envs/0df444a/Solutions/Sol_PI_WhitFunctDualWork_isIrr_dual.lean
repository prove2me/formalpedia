-- Prove2me | solution 1 for PI.WhitFunctDualWork.isIrr_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:06.752354+00:00
-- url     : https://prove2.me/submissions/ab23a40d-11e6-4abe-b4d1-39d5a2bef869

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WhitFunctDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WhittakerFunctionalDual_StableOfIrreducible
import Theorems.Thm_PI_WhitFunctDualWork_stable_of_irreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.WhitFunctDualWork
open Formalism.L2.SG.GGMirabolic
namespace PI.WhitFunctDualWork
theorem _root_.solution {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ G V) (h : π.IsIrreducible) :
    Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr (Representation.dual π) := by
  obtain ⟨hnt, hst⟩ := stable_of_irreducible π h
  refine ⟨Module.nontrivial_of_finrank_pos (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_pos),
    fun W hW => ?_⟩
  have hU : ∀ g, ∀ v ∈ W.dualCoannihilator, π g v ∈ W.dualCoannihilator := by
    intro g v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using hv _ (hW g⁻¹ f hf)
  have hW' : W = W.dualCoannihilator.dualAnnihilator :=
    Subspace.dualCoannihilator_dualAnnihilator_eq.symm
  rcases hst _ hU with h0 | h0
  · right
    rw [hW', h0, Submodule.dualAnnihilator_bot]
  · left
    rw [hW', h0, Submodule.dualAnnihilator_top]
end PI.WhitFunctDualWork
