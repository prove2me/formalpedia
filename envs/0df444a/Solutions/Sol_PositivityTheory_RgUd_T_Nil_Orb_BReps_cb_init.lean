-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_init
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:58.366081+00:00
-- url     : https://prove2.me/submissions/0a0e3ded-f7b5-47a5-8a13-59b8d8a709cd

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbIsChainApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbExistsChainOfGen
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_single
import Theorems.Thm_P2M_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_apply__4e7af1fbc80f
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_len


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
theorem _root_.solution (N : W →ₗ[E] W) {ι : Type} [Fintype ι] {l : ι → ℕ}
    (B0 : Module.Basis (Σ a, Fin (l a)) E W) (hB0 : IsChain N l B0) (hl : ∀ a, 0 < l a) (v : W) :
    ∃ (y : ι → W) (s : ι → ℕ), (∀ a, (N ^ l a) (y a) = 0) ∧
      (∀ a, B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E (Set.range (cbFam N l y)) ⊔ LinearMap.range N) ∧
      (∀ a, s a ≤ l a) ∧ v = ∑ a, (N ^ s a) (y a) := by
  have H : ∀ a, ∃ s ≤ l a, ∃ y : W, (N ^ l a) y = 0 ∧
      (N ^ s) y = ∑ i : Fin (l a), B0.repr v ⟨a, i⟩ • (N ^ (i : ℕ)) (B0 ⟨a, ⟨0, hl a⟩⟩) ∧
      B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E {y} ⊔ LinearMap.range N :=
    fun a => cb_single N (l a) _ (cb_isChain_len N hB0 a (hl a)) _
  choose s hs y hy0 hys hyu using H
  refine ⟨y, s, hy0, fun a => ?_, hs, ?_⟩
  · have hle : span E {y a} ≤ span E (Set.range (cbFam N l y)) := by
      rw [span_le, Set.singleton_subset_iff]
      exact subset_span ⟨⟨a, ⟨0, hl a⟩⟩, by simp [cbFam]⟩
    exact sup_le_sup_right hle _ (hyu a)
  · conv_lhs => rw [← B0.sum_repr v]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hys]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cb_isChain_apply' N hB0 a (hl a) i]
end PositivityTheory.RgUd.T.Nil.Orb.BReps
