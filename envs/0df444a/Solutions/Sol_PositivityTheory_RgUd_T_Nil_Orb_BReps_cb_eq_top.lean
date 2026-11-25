-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:50.33908+00:00
-- url     : https://prove2.me/submissions/84349590-3aa8-4539-8dd6-2070f553de83

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbIsChainApply
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_pow_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
open Module Submodule
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution (N : W →ₗ[E] W) (hN : IsNilpotent N) (S : Submodule E W)
    (hS : ∀ x ∈ S, N x ∈ S) (h : S ⊔ LinearMap.range N = ⊤) : S = ⊤ := by
  have key : ∀ k : ℕ, S ⊔ LinearMap.range (N ^ k) = ⊤ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id, sup_top_eq]
    | succ k ih =>
      rw [eq_top_iff]
      intro w _
      have hw : w ∈ S ⊔ LinearMap.range N := h ▸ Submodule.mem_top
      obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨z', rfl⟩ := hz
      have hz' : z' ∈ S ⊔ LinearMap.range (N ^ k) := ih ▸ Submodule.mem_top
      obtain ⟨x2, hx2, z2, hz2, rfl⟩ := Submodule.mem_sup.mp hz'
      obtain ⟨z3, rfl⟩ := hz2
      rw [map_add]
      apply Submodule.mem_sup.mpr
      refine ⟨x + N x2, S.add_mem hx (hS _ hx2), (N ^ (k + 1)) z3, ⟨z3, rfl⟩, ?_⟩
      rw [cb_pow_succ, add_assoc]
  obtain ⟨K, hK⟩ := hN
  have := key K
  rwa [hK, LinearMap.range_zero, sup_bot_eq] at this
end PositivityTheory.RgUd.T.Nil.Orb.BReps
