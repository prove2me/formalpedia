-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.cb_exists_chain_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:54.662012+00:00
-- url     : https://prove2.me/submissions/4b9a5dbe-add5-4708-8b43-61df387c30cb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbIsChainApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbExistsChainOfGen
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_eq_top
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_apply
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_of_fam
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_pow_succ
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_pow_zero_of_le


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
theorem _root_.solution (N : W →ₗ[E] W) (hN : IsNilpotent N) {ι : Type} [Fintype ι] {l : ι → ℕ}
    (B0 : Module.Basis (Σ a, Fin (l a)) E W) (hB0 : IsChain N l B0) (hl : ∀ a, 0 < l a) (y : ι → W)
    (hy0 : ∀ a, (N ^ l a) (y a) = 0)
    (hy : ∀ a, B0 ⟨a, ⟨0, hl a⟩⟩ ∈ span E (Set.range (cbFam N l y)) ⊔ LinearMap.range N) :
    ∃ B : Module.Basis (Σ a, Fin (l a)) E W, IsChain N l B ∧ ∀ p, B p = cbFam N l y p := by
  set S := span E (Set.range (cbFam N l y)) with hSdef
  have hS : ∀ x ∈ S, N x ∈ S := by
    intro x hx
    have : S ≤ S.comap N := by
      rw [hSdef, span_le]
      rintro _ ⟨p, rfl⟩
      show N (cbFam N l y p) ∈ S
      simp only [cbFam]
      rw [cb_pow_succ]
      by_cases h : (p.2 : ℕ) + 1 < l p.1
      · exact subset_span ⟨⟨p.1, ⟨p.2 + 1, h⟩⟩, rfl⟩
      · rw [cb_pow_zero_of_le N (hy0 p.1) (by omega)]; exact S.zero_mem
    exact this hx
  have htop : S ⊔ LinearMap.range N = ⊤ := by
    rw [eq_top_iff, ← B0.span_eq, span_le]
    rintro _ ⟨⟨a, ⟨i, hi⟩⟩, rfl⟩
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; exact hy a
    · apply Submodule.mem_sup_right
      rw [cb_isChain_apply N hB0 a (hl a) i hi]
      refine ⟨(N ^ (i - 1)) (B0 ⟨a, ⟨0, hl a⟩⟩), ?_⟩
      rw [cb_pow_succ, show i - 1 + 1 = i by omega]
  have hST : S = ⊤ := cb_eq_top N hN S hS htop
  have hli : LinearIndependent E (cbFam N l y) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (by rw [← hSdef, hST])
      (by rw [Module.finrank_eq_card_basis B0])
  refine ⟨Basis.mk hli (by rw [← hSdef, hST]), ?_, fun p => by simp⟩
  exact cb_isChain_of_fam N l y hy0 _ (fun p => by simp)
end PositivityTheory.RgUd.T.Nil.Orb.BReps
