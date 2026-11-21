-- Prove2me | solution 1 for OnlineTransportation1195.Main.transportation_four_m_minus_five
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T09:58:14.877175+00:00
-- url     : https://prove2.me/submissions/a71e311b-e080-4916-88a1-afb394a32ba2

import Theorems.Thm_OnlineTransportation1195_Main_optimal_point_count_ratio
import Theorems.Thm_OnlineTransportation1195_Main_nearest_garage_reduction

section
namespace OnlineTransportation1195.Dev.Goal
open OnlineTransportation1195.Main OnlineTransportation1195.Main.TransportationInstance

theorem pointRatio_small (n : ℕ) (hn : n ≤ 1) : PointRatio n 0 := by
  refine ⟨le_refl _, fun I => ⟨fun _ => Equiv.refl _, fun r q t _ => rfl, ?_⟩⟩
  intro r
  have hs : Subsingleton (Fin n) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with h | h <;> subst h <;> infer_instance
  have hc : ∀ a, I.cost r a = 0 := by
    intro a
    unfold TransportationInstance.cost
    letI := I.metric
    refine Finset.sum_eq_zero fun t _ => ?_
    exact (dist_eq_zero.mpr (Subsingleton.elim _ _))
  simp [hc]

theorem chk_aux (n : ℕ) (I : TransportationInstance n)
    (hm : 2 ≤ I.garages.card) :
    ∃ A : Policy I, IsCausal I A ∧
      Competitive I A (4 * (I.garages.card : ℝ) - 5) := by
  have h := nearest_garage_reduction (fun m => max (2 * (m : ℝ) - 3) 0) (by
    intro m
    by_cases hm : 2 ≤ m
    · have := (optimal_point_count_ratio m hm).1
      have e : max (2 * (m : ℝ) - 3) 0 = 2 * (m : ℝ) - 3 := by
        have : (2 : ℝ) ≤ m := by exact_mod_cast hm
        exact max_eq_left (by linarith)
      rw [e]; exact this
    · have h0 : max (2 * (m : ℝ) - 3) 0 = 0 := by
        have : (m : ℝ) ≤ 1 := by exact_mod_cast (by omega : m ≤ 1)
        exact max_eq_right (by linarith)
      rw [h0]; exact pointRatio_small m (by omega))
  obtain ⟨_, h2⟩ := h
  obtain ⟨A, hA, hc⟩ := h2 n I
  refine ⟨A, hA, ?_⟩
  have : (2 : ℝ) ≤ I.garages.card := by exact_mod_cast hm
  have e : 2 * max (2 * (I.garages.card : ℝ) - 3) 0 + 1 = 4 * (I.garages.card : ℝ) - 5 := by
    rw [max_eq_left (by linarith)]; ring
  simpa [e] using hc

end OnlineTransportation1195.Dev.Goal

namespace OnlineTransportation1195.Main
theorem chk_transportation_four_m_minus_five (n : ℕ) (I : TransportationInstance n)
    (hm : 2 ≤ I.garages.card) :
    ∃ A : Policy I, IsCausal I A ∧
      Competitive I A (4 * (I.garages.card : ℝ) - 5) :=
  OnlineTransportation1195.Dev.Goal.chk_aux n I hm
end OnlineTransportation1195.Main
end

theorem solution : type_of% @OnlineTransportation1195.Main.chk_transportation_four_m_minus_five := @OnlineTransportation1195.Main.chk_transportation_four_m_minus_five
