-- Prove2me | solution 1 for Value.blocks_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:53.778785+00:00
-- url     : https://prove2.me/submissions/262469f6-6d59-4e17-bcb3-7c3d5efff5ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Value_thetaAt_eq_readBlocks
import Theorems.Thm_Value_mem_mD_iff
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_mem_tuples
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_pr_of_lt
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
namespace Value
theorem _root_.solution (hSB : StSameBlock) (Np : Procs C) (c : C) (hK0 : 0 < K) (x L : ℕ) {θ : Fin g × Fin g → List Bool} (hθ : θ ∈ blockStrings N (Paper.grouping hK0 x)) (Λ : Fin K × Fin K → List Bool) :
    (Λ ∈ edgeStrings K L ∧ AppendedZero g Np c x Λ ∧ readBlocks Np c hK0 x Λ = θ) ↔ ∀ p, EdgeReads Np c hK0 x L θ p (Λ p) := by
  have hread : ∀ a b : Fin g, Paper.grouping hK0 x a < Paper.grouping hK0 x b →
      readBlocks Np c hK0 x Λ (pr a b) = mdec K g Np.toPaperNetwork c x (Paper.grouping hK0 x a) (Paper.grouping hK0 x b) (Λ (Paper.grouping hK0 x a, Paper.grouping hK0 x b)) (a, b) := by
    intro a b hab
    rw [← thetaAt_eq_readBlocks hSB Np c hK0 x Λ hab.ne]
    unfold thetaAt Groundwork.star pr
    rw [min_eq_left hab.le, max_eq_right hab.le, if_pos hab]
  constructor
  · rintro ⟨hΛ, hA, hR⟩ p
    refine ⟨fun hp => ⟨(mem_mD_iff _ _ _ _ _ _ _).2 ⟨mem_words.1 (((mem_tuples _ _ _ _).1 hΛ p).1 hp), ?_⟩, ?_⟩, fun hp => ((mem_tuples _ _ _ _).1 hΛ p).2 hp⟩
    · have h1 := hA p.1 p.2 hp.ne'
      unfold appendedBits Groundwork.star pr at h1
      rw [min_eq_left hp.le, max_eq_right hp.le] at h1
      exact h1
    · rintro q ⟨h1, h2⟩
      have h3 := hread q.1 q.2 (by rw [h1, h2]; exact hp)
      rw [h1, h2, hR] at h3
      exact h3.symm
  · intro H
    have HH : ∀ γ γ' : Fin K, γ < γ' → Λ (γ, γ') ∈ mD K g Np.toPaperNetwork c x L γ γ' ∧
        ∀ a b : Fin g, Paper.grouping hK0 x a = γ → Paper.grouping hK0 x b = γ' → mdec K g Np.toPaperNetwork c x γ γ' (Λ (γ, γ')) (a, b) = θ (pr a b) :=
      fun γ γ' h => ⟨((H (γ, γ')).1 h).1, fun a b h1 h2 => ((H (γ, γ')).1 h).2 (a, b) ⟨h1, h2⟩⟩
    refine ⟨(mem_tuples _ _ _ _).2 fun p => ⟨fun hp => mem_words.2 ((mem_mD_iff _ _ _ _ _ _ _).1 ((H p).1 hp).1).1, (H p).2⟩, ?_, ?_⟩
    · intro γ γ' hne
      exact ((mem_mD_iff _ _ _ _ _ _ _).1 (HH _ _ (min_lt_max.2 hne.symm)).1).2
    · funext q
      by_cases hq : Across (Paper.grouping hK0 x) q
      · rcases lt_or_gt_of_ne hq.2 with h | h
        · have h1 := (hread q.1 q.2 h).trans ((HH _ _ h).2 q.1 q.2 rfl rfl)
          rw [(pr_of_lt hq.1).1] at h1
          exact h1
        · have h1 := (hread q.2 q.1 h).trans ((HH _ _ h).2 q.2 q.1 rfl rfl)
          rw [(pr_of_lt hq.1).2] at h1
          exact h1
      · exact (if_neg hq).trans (((mem_tuples _ _ _ _).1 hθ q).2 hq).symm
end Value
