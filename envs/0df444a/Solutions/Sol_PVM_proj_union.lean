-- Prove2me | solution 1 for PVM.proj_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:44.766826+00:00
-- url     : https://prove2.me/submissions/7feeae7b-27f1-4ccf-9c93-bf37c177c343

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_Spectral_PVM_Basic

set_option autoImplicit false
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hdisj : Disjoint S T) :
    E_pvm.proj (S ∪ T) = E_pvm.proj S + E_pvm.proj T := by
  let sets : ℕ → Set ℝ
    | 0 => S
    | 1 => T
    | _ => ∅
  have hmeas : ∀ i, MeasurableSet (sets i) := by
    rintro (_ | (_ | _))
    · exact hS
    · exact hT
    · exact MeasurableSet.empty
  have hpairwise : Pairwise (Disjoint on sets) := by
    rintro i j hij
    rcases i with _ | (_ | i) <;> rcases j with _ | (_ | j)
    · exact (hij rfl).elim
    · exact hdisj
    · exact disjoint_bot_right
    · exact hdisj.symm
    · exact (hij rfl).elim
    · exact disjoint_bot_right
    · exact disjoint_bot_left
    · exact disjoint_bot_left
    · exact disjoint_bot_left
  have hunion : (⋃ i, sets i) = S ∪ T := by
    ext t
    constructor
    · rw [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      rcases i with _ | (_ | i)
      · exact Set.mem_union_left T hi
      · exact Set.mem_union_right S hi
      · exact False.elim hi
    · intro ht
      rcases ht with ht | ht
      · rw [Set.mem_iUnion]
        exact ⟨0, ht⟩
      · rw [Set.mem_iUnion]
        exact ⟨1, ht⟩
  apply ContinuousLinearMap.ext
  intro x
  have hlim := E_pvm.countably_additive sets hmeas hpairwise x
  rw [hunion] at hlim
  have hsets (n : ℕ) (hn : 2 ≤ n) : sets n = ∅ := by
    rcases n with _ | (_ | n)
    · omega
    · omega
    · rfl
  have hsum : ∀ n ≥ 2,
      (∑ i ∈ Finset.range n, E_pvm.proj (sets i) x) =
        E_pvm.proj S x + E_pvm.proj T x := by
    intro n hn
    obtain ⟨k, rfl⟩ := exists_add_of_le hn
    induction k with
    | zero =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        change 0 + E_pvm.proj S x + E_pvm.proj T x = _
        rw [zero_add]
    | succ k ih =>
        rw [show 2 + (k + 1) = (2 + k) + 1 by omega, Finset.sum_range_succ,
          ih (by omega), hsets (2 + k) (by omega)]
        rw [E_pvm.empty, zero_apply, add_zero]
  have hconst : Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n, E_pvm.proj (sets i) x)
      Filter.atTop (nhds (E_pvm.proj S x + E_pvm.proj T x)) :=
    tendsto_atTop_of_eventually_const hsum
  exact tendsto_nhds_unique hlim hconst
end PVM
