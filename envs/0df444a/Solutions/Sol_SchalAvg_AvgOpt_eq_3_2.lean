-- Prove2me | solution 1 for SchalAvg.AvgOpt.eq_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:45:11.731346+00:00
-- url     : https://prove2.me/submissions/7a9c1d2a-02bb-4473-b72d-d987b31d0183

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SAeq32

open SchalAvg.AvgOpt

theorem main {S A : Type*} [MetricSpace S] [MeasurableSpace S] [MeasurableSpace A]
    (M : Model S A) (β : ℕ → ℝ) (x : S) :
    MonotoneOn (fun n : ℕ => ⨅ k ≥ n, wBall M β n k x) (Set.Ici 1) ∧
    Tendsto (fun n : ℕ => ⨅ k ≥ n, wBall M β n k x) atTop (𝓝 (wLow M β x)) := by
  set F := fun n : ℕ => ⨅ k ≥ n, wBall M β n k x with hF
  have hball : ∀ n m : ℕ, 1 ≤ n → n ≤ m →
      Metric.closedBall x (1 / (m : ℝ)) ⊆ Metric.closedBall x (1 / (n : ℝ)) := by
    intro n m hn hnm
    apply Metric.closedBall_subset_closedBall
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le this (by exact_mod_cast hnm)
  have hmono : MonotoneOn F (Set.Ici 1) := by
    intro n hn m _ hnm
    simp only [hF]
    apply le_iInf₂
    intro k hk
    refine (iInf₂_le k (le_trans hnm hk)).trans ?_
    unfold wBall
    exact biInf_mono (hball n m hn hnm)
  refine ⟨hmono, ?_⟩
  -- the liminf as a supremum over a basis
  have hb := (atTop_basis (α := ℕ)).prod (Metric.nhds_basis_closedBall (x := x))
  have hL : wLow M β x = ⨆ n : ℕ, F (n + 1) := by
    unfold wLow
    rw [hb.liminf_eq_iSup_iInf]
    apply le_antisymm
    · apply iSup₂_le
      rintro ⟨N, ε⟩ ⟨-, hε⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      refine le_trans ?_ (le_iSup _ (max N n))
      simp only [hF]
      apply le_iInf₂
      intro k hk
      unfold wBall
      apply le_iInf₂
      intro y hy
      apply iInf₂_le (k, y)
      refine ⟨Set.mem_Ici.2 (le_trans (le_trans (le_max_left _ _) (Nat.le_succ _)) hk), ?_⟩
      refine Metric.closedBall_subset_closedBall ?_ hy
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : ((n : ℝ) + 1) ≤ ((max N n + 1 : ℕ) : ℝ) := by
        push_cast; gcongr; exact_mod_cast le_max_right N n
      calc 1 / ((max N n + 1 : ℕ) : ℝ) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le h1 h2
        _ ≤ ε := hn.le
    · apply iSup_le
      intro n
      refine le_trans ?_ (le_iSup₂ (f := fun (i : ℕ × ℝ) (_ : True ∧ 0 < i.2) =>
        ⨅ a ∈ Set.Ici i.1 ×ˢ Metric.closedBall x i.2, wβ M (β a.1) a.2)
        (n + 1, 1 / ((n + 1 : ℕ) : ℝ)) ⟨trivial, by positivity⟩)
      apply le_iInf₂
      rintro ⟨k, y⟩ ⟨hk, hy⟩
      simp only [hF]
      refine (iInf₂_le k hk).trans ?_
      unfold wBall
      exact iInf₂_le y hy
  rw [hL]
  have hmono' : Monotone (fun n : ℕ => F (n + 1)) := fun a b hab =>
    hmono (Set.mem_Ici.2 (by omega)) (Set.mem_Ici.2 (by omega)) (by omega)
  exact (tendsto_add_atTop_iff_nat 1).1 (tendsto_atTop_iSup hmono')

end SAeq32

open SchalAvg.AvgOpt in
theorem solution {S A : Type*} [MetricSpace S] [MeasurableSpace S] [MeasurableSpace A]
    (M : Model S A) (β : ℕ → ℝ) (x : S) :
    MonotoneOn (fun n : ℕ => ⨅ k ≥ n, wBall M β n k x) (Set.Ici 1) ∧
    Tendsto (fun n : ℕ => ⨅ k ≥ n, wBall M β n k x) atTop (𝓝 (wLow M β x)) :=
  SAeq32.main M β x
