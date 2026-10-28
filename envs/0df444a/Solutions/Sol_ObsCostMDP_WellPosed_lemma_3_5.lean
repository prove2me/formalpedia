-- Prove2me | solution 1 for ObsCostMDP.WellPosed.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:28:37.110969+00:00
-- url     : https://prove2.me/submissions/6684c738-9489-4a83-aabc-1693ffdecf76

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Definitions.Def_ObsCostMDP_WellPosed_Truncated

namespace Aux_ObsCostMDP_WellPosed_lemma_3_5
open ObsCostMDP.WellPosed

theorem bdd {N : ℕ} {X A : Type*} [Fintype X] [Fintype A] (u : Fin N → X → A → ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ m y a, |zeroExt u m y a| ≤ K := by
  refine ⟨∑ p : Fin N × X × A, |u p.1 p.2.1 p.2.2|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro m y a
  unfold zeroExt
  split_ifs with h
  · exact Finset.single_le_sum (f := fun p : Fin N × X × A => |u p.1 p.2.1 p.2.2|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (⟨m - 1, by omega⟩, y, a))
  · simp only [abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

end Aux_ObsCostMDP_WellPosed_lemma_3_5

open ObsCostMDP.WellPosed Aux_ObsCostMDP_WellPosed_lemma_3_5 in
theorem solution {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : Driver X A) (β : ℝ) (hF : Assumption32 F β) (N : ℕ) :
    Property35 (restrictDriver F N) β := by
  refine ⟨hF.1, ?_⟩
  intro u v nb lb ab hmax hδ
  obtain ⟨Ku, hKu0, hKu⟩ := bdd u
  obtain ⟨Kv, hKv0, hKv⟩ := bdd v
  have hu' : IsBounded (fun m y j => zeroExt u m y j - (u nb lb ab - v nb lb ab)) := by
    refine ⟨Ku + |u nb lb ab - v nb lb ab|, fun m y j => ?_⟩
    have h1 := abs_le.mp (hKu m y j)
    have h2 := neg_abs_le (u nb lb ab - v nb lb ab)
    have h3 := le_abs_self (u nb lb ab - v nb lb ab)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hv' : IsBounded (zeroExt v) := ⟨Kv, hKv⟩
  have hle : ∀ m y j, zeroExt u m y j - (u nb lb ab - v nb lb ab) ≤ zeroExt v m y j := by
    intro m y j
    unfold zeroExt
    split_ifs with h
    · linarith [hmax ⟨m - 1, by omega⟩ y j]
    · linarith
  have key := hF.2.1 (nb.val + 1) lb _ _ hu' hv' hle (u nb lb) (v nb lb) ab
    (fun j => hmax nb lb j) hδ
  simp only [sub_add_cancel] at key
  exact key
