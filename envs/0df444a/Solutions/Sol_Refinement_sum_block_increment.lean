-- Prove2me | solution 1 for Refinement.sum_block_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:30:14.085242+00:00
-- url     : https://prove2.me/submissions/9c8bcaac-2f89-4212-91ef-962ac15c774a

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F010
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
noncomputable section

/-- The refinement block telescopes between its original partition endpoints. -/
theorem solution {a b : ℝ} {α : ℝ → ℝ} {P P' : Partition a b}
    (R : Refinement P P') (i : Fin P.n) :
    Finset.sum (R.block i)
      (fun j => α (P'.pts j.succ) - α (P'.pts j.castSucc)) =
      α (P.pts i.succ) - α (P.pts i.castSucc) := by
  classical
  let lo : ℕ := (R.index i.castSucc).val
  let hi : ℕ := (R.index i.succ).val
  have hlt : lo < hi := R.strictMono_index Fin.castSucc_lt_succ
  have hhi : hi ≤ P'.n := Nat.le_of_lt_succ (R.index i.succ).isLt
  let u : ℕ → ℝ :=
    fun k => if hk : k < P'.n + 1 then α (P'.pts ⟨k, hk⟩) else 0
  have hs :
      Finset.sum (R.block i) (fun j => α (P'.pts j.succ) - α (P'.pts j.castSucc)) =
        ∑ t ∈ Finset.range (hi - lo),
          (u (lo + (t + 1)) - u (lo + t)) := by
    unfold Refinement.block
    dsimp [lo, hi]
    rw [Finset.sum_image]
    · trans (Finset.sum ((Finset.range (hi - lo)).attach)
          (fun t => u (lo + (t.1 + 1)) - u (lo + t.1)))
      · apply Finset.sum_congr rfl
        intro t ht
        have htlt : t.1 < hi - lo := Finset.mem_range.mp t.2
        have hleft : lo + t.1 < P'.n + 1 := by omega
        have hright : lo + (t.1 + 1) < P'.n + 1 := by omega
        dsimp [u]
        rw [dif_pos hright, dif_pos hleft]
        apply congrArg₂ Sub.sub
          (congrArg (fun z : Fin (P'.n + 1) => α (P'.pts z))
            (Fin.ext (by simp [Fin.succ]; omega)))
          (congrArg (fun z : Fin (P'.n + 1) => α (P'.pts z))
            (Fin.ext (by simp [Fin.castSucc, lo])))
      · simpa only using
          (Finset.sum_attach (s := Finset.range (hi - lo))
            (f := fun t => u (lo + (t + 1)) - u (lo + t)))
    · intro x hx y hy hxy
      apply Subtype.ext
      have hval := congrArg Fin.val hxy
      exact Nat.add_left_cancel hval
  rw [hs, sum_range_sub_from]
  rw [Nat.add_sub_of_le (le_of_lt hlt)]
  have hlo' : lo < P'.n + 1 := (R.index i.castSucc).isLt
  have hhi' : hi < P'.n + 1 := (R.index i.succ).isLt
  dsimp [u]
  rw [dif_pos hhi', dif_pos hlo']
  have heq_hi : (⟨hi, hhi'⟩ : Fin (P'.n + 1)) = R.index i.succ := Fin.ext rfl
  have heq_lo : (⟨lo, hlo'⟩ : Fin (P'.n + 1)) = R.index i.castSucc := Fin.ext rfl
  rw [heq_hi, heq_lo, ← R.index_spec i.succ, ← R.index_spec i.castSucc]
