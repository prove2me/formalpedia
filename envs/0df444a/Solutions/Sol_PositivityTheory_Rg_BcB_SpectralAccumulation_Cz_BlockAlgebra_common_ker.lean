-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.common_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:30:00.981181+00:00
-- url     : https://prove2.me/submissions/c0391a20-8317-4f07-b5ea-c3750a251e6d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PBlocksAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
theorem _root_.solution (L : List (Module.End ℂ M)) (hL : ∀ N ∈ L, IsNilpotent N)
    (hc : ∀ N ∈ L, ∀ N' ∈ L, Commute N N') (Q : Submodule ℂ M) (hQ : Q ≠ ⊥)
    (hQL : ∀ N ∈ L, ∀ y ∈ Q, N y ∈ Q) : ∃ y ∈ Q, y ≠ 0 ∧ ∀ N ∈ L, N y = 0 := by
  induction L generalizing Q with
  | nil =>
    obtain ⟨y, hy, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
    exact ⟨y, hy, h0, by simp⟩
  | cons N L ih =>
    classical
    obtain ⟨y, hy, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
    obtain ⟨n, hn⟩ := hL N List.mem_cons_self
    have hex : ∃ k, (N ^ k) y = 0 := ⟨n, by rw [hn]; rfl⟩
    set k := Nat.find hex with hk
    have hk0 : k ≠ 0 := by
      intro h
      have h1 := Nat.find_spec hex
      rw [← hk, h, pow_zero, Module.End.one_apply] at h1
      exact h0 h1
    have hpowQ : ∀ j, (N ^ j) y ∈ Q := by
      intro j
      induction j with
      | zero => simpa using hy
      | succ j ihj =>
        rw [pow_succ', Module.End.mul_apply]
        exact hQL N List.mem_cons_self _ ihj
    have hy1 : (N ^ (k - 1)) y ≠ 0 := Nat.find_min hex (by omega)
    have hNy1 : N ((N ^ (k - 1)) y) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
      exact Nat.find_spec hex
    set Q' := Q ⊓ LinearMap.ker N with hQ'
    have hQ'0 : Q' ≠ ⊥ := by
      intro h
      have hm : (N ^ (k - 1)) y ∈ Q' := ⟨hpowQ _, hNy1⟩
      rw [h] at hm
      exact hy1 ((Submodule.mem_bot ℂ).1 hm)
    have hLQ' : ∀ N' ∈ L, ∀ z ∈ Q', N' z ∈ Q' := by
      intro N' hN' z hz
      refine ⟨hQL N' (List.mem_cons_of_mem _ hN') z hz.1, ?_⟩
      change N (N' z) = 0
      rw [← Module.End.mul_apply, (hc N List.mem_cons_self N' (List.mem_cons_of_mem _ hN')).eq,
        Module.End.mul_apply]
      have : N z = 0 := hz.2
      rw [this, map_zero]
    obtain ⟨z, hz, hz0, hzL⟩ := ih (fun N' hN' => hL N' (List.mem_cons_of_mem _ hN'))
      (fun N' hN' N'' hN'' => hc N' (List.mem_cons_of_mem _ hN') N'' (List.mem_cons_of_mem _ hN'')) Q' hQ'0 hLQ'
    refine ⟨z, hz.1, hz0, fun N' hN' => ?_⟩
    rcases List.mem_cons.1 hN' with rfl | h
    · exact hz.2
    · exact hzL N' h
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
