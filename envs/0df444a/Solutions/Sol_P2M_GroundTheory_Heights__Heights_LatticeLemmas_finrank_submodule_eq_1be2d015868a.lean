-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_submodule_eq_1be2d015868a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:43.627029+00:00
-- url     : https://prove2.me/submissions/ea85cbba-0295-4435-a1d2-76648e9d3f2e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    (F : Submodule R M) (hF : ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x ∈ F) :
    Module.finrank R F = Module.finrank R M := by
  have h0 : Module.rank R (M ⧸ F) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨x, rfl⟩ := F.mkQ_surjective x
    obtain ⟨a, ha, hax⟩ := hF x
    refine ⟨a, ha, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hax
  have h := rank_quotient_add_rank_of_isDomain F
  rw [h0, zero_add] at h
  simp only [Module.finrank, h]
end GroundTheory.Heights₂.Heights.LatticeLemmas
