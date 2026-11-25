-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:39.027869+00:00
-- url     : https://prove2.me/submissions/4f9f96d6-f764-467d-81c7-56c036c31bf2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_CbExistsChainOfGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsChainsOfRange
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ChainB
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_step
import Theorems.Thm_GlobalTheory_CompanionTheory_JordanChain_exists_chain_basis
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_exists_chain_of_gen
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_init
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_cb_isChain_of_fam


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
open Module Submodule
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution [FiniteDimensional E W] (N : W →ₗ[E] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W), IsChain N l B ∧
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧ (∀ a b, s a ≤ s b + (l a - l b)) ∧
      v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0 := by
  classical
  obtain ⟨ι, _, e, u, he, hu0, hli, hsp⟩ := GlobalTheory.CompanionTheory.JordanChain.exists_chain_basis N hN
  let B0 : Module.Basis (Σ a, Fin (e a)) E W := Basis.mk hli (by rw [hsp])
  have hB0p : ∀ p, B0 p = cbFam N e u p := fun p => by simp [B0, cbFam]
  have hB0 : IsChain N e B0 := cb_isChain_of_fam N e u hu0 B0 hB0p
  obtain ⟨y, s, hy0, hyg, hs, hv⟩ := cb_init N B0 hB0 he v
  obtain ⟨B1, hB1, hB1y⟩ := cb_exists_chain_of_gen N hN B0 hB0 he y hy0 hyg
  have hex : ∃ k, ∃ (y : ι → W) (s : ι → ℕ), ((∀ a, (N ^ e a) (y a) = 0) ∧
      (∃ B : Module.Basis (Σ a, Fin (e a)) E W, IsChain N e B ∧ ∀ p, B p = cbFam N e y p) ∧
      (∀ a, s a ≤ e a) ∧ v = ∑ a, (N ^ s a) (y a)) ∧ ∑ a, s a = k :=
    ⟨_, y, s, ⟨hy0, ⟨B1, hB1, hB1y⟩, hs, hv⟩, rfl⟩
  obtain ⟨y, s, ⟨hy0, ⟨B, hB, hBy⟩, hs, hv⟩, hk⟩ := Nat.find_spec hex
  have hC : ∀ a b, s a ≤ s b + (e a - e b) := by
    intro a b
    by_contra hab
    push Not at hab
    obtain ⟨y', s', h1, h2, h3, h4, h5⟩ := cb_step N hN he v y s hy0 B hB hBy hs hv a b hab
    exact Nat.find_min hex (hk ▸ h5) ⟨y', s', ⟨h1, h2, h3, h4⟩, rfl⟩
  refine ⟨ι, inferInstance, e, s, B, hB, he, hs, hC, ?_⟩
  rw [hv]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [hBy]; rfl
  · rw [show s a = e a by have := hs a; omega, hy0]
end PositivityTheory.RgUd.T.Nil.Orb.BReps
