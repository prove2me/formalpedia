-- Prove2me | solution 1 for PerishShip.Waste.theorem_1_warehouse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:15:23.915059+00:00
-- url     : https://prove2.me/submissions/67a85395-03ab-47aa-b195-98ef291161c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PerishShip_Waste_Model
import Theorems.Thm_PerishShip_Waste_avg_optimal_of_pathwise_regret
import Theorems.Thm_PerishShip_Waste_sofFull_pathwise_regret

open PerishShip.Waste

namespace PerishShipT1WAux

lemma shift_sum_le (n : ℕ) (g : Fin n → ℕ) :
    ∑ i : Fin n, (if h : i.val = 0 then 0 else g ⟨i.val - 1, by omega⟩) ≤ ∑ i, g i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc (f := g)]
    have h0 : (if h : (0 : Fin (m+1)).val = 0 then 0 else g ⟨(0 : Fin (m+1)).val - 1, by omega⟩) = 0 := by
      simp
    rw [h0, zero_add]
    have h1 : ∀ x : Fin m, (if h : (Fin.succ x).val = 0 then 0
        else g ⟨(Fin.succ x).val - 1, by omega⟩) = g x.castSucc := by
      intro x
      rw [dif_neg (by simp)]
      rfl
    simp_rw [h1]
    exact Nat.le_add_right _ _

lemma ageShift_sum_le {P : Params} (g : Vec P) : ∑ i, ageShift g i ≤ ∑ i, g i := by
  unfold ageShift
  exact shift_sum_le P.N g

lemma xbar_sum_le {P : Params} (s : State P) (hs : s.Feasible) : ∑ i, xbar s i ≤ P.SW := by
  have h : ∀ i, xbar s i = s.x i + (if i.val = 0 then P.SW - ∑ j, s.x j else 0) := by
    intro i
    unfold xbar
    by_cases hi : i.val = 0
    · simp [hi, (hs.1 i hi).1]
    · simp [hi]
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  have h2 : ∑ i : Fin P.N, (if i.val = 0 then P.SW - ∑ j, s.x j else 0) ≤ P.SW - ∑ j, s.x j := by
    by_cases hN : P.N = 0
    · have : IsEmpty (Fin P.N) := by rw [hN]; infer_instance
      simp
    · have hz : ∀ i : Fin P.N, (i.val = 0 ↔ i = ⟨0, Nat.pos_of_ne_zero hN⟩) := by
        intro i; constructor
        · intro h; exact Fin.ext h
        · intro h; rw [h]
      simp_rw [hz]
      simp
  have h3 := hs.2.1
  omega

lemma next_feasible {P : Params} (s : State P) (q : Vec P) (lam : ℕ) (hs : s.Feasible)
    (hq : ShipFeasible s q) : (next s q lam).Feasible := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp [next, ageShift, hi]
  · calc ∑ i, (next s q lam).x i = ∑ i, ageShift (fun i => xbar s i - q i) i := rfl
      _ ≤ ∑ i, (xbar s i - q i) := ageShift_sum_le _
      _ ≤ ∑ i, xbar s i := Finset.sum_le_sum (fun i _ => Nat.sub_le _ _)
      _ ≤ P.SW := xbar_sum_le s hs
  · calc ∑ i, (next s q lam).y i = ∑ i, ageShift (left s q lam) i := rfl
      _ ≤ ∑ i, left s q lam i := ageShift_sum_le _
      _ ≤ ∑ i, z s q i := Finset.sum_le_sum (fun i _ => Nat.sub_le _ _)
      _ = ∑ i, s.y i + ∑ i, q i := by simp [z, Finset.sum_add_distrib]
      _ ≤ P.L := by have := hq.2; omega

/-- Telescoping bound for an antitone sequence. -/
lemma tele (h : ℕ → ℕ) (hh : Antitone h) (n : ℕ) :
    ∑ k ∈ Finset.range n, (h k - h (k + 1)) = h 0 - h n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 := hh (Nat.zero_le n)
    have h2 := hh (Nat.le_add_right n 1)
    omega

lemma sofFull_sum_le {P : Params} (s : State P) : ∑ i, sofFull s i ≤ shipTotal s := by
  set T := shipTotal s
  let H : ℕ → ℕ := fun k => min T (∑ j ∈ Finset.univ.filter (fun j : Fin P.N => k ≤ j.val), xbar s j)
  have hH : Antitone H := by
    intro a b hab
    simp only [H]
    apply min_le_min_left
    apply Finset.sum_le_sum_of_subset
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega
  have hpt : ∀ i : Fin P.N, sofFull s i = H i.val - H (i.val + 1) := by
    intro i
    have hIoi : ∑ j ∈ Finset.Ioi i, xbar s j =
        ∑ j ∈ Finset.univ.filter (fun j : Fin P.N => i.val + 1 ≤ j.val), xbar s j := by
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val]
        omega
      · intros; rfl
    have hIci : ∑ j ∈ Finset.univ.filter (fun j : Fin P.N => i.val ≤ j.val), xbar s j =
        xbar s i + ∑ j ∈ Finset.univ.filter (fun j : Fin P.N => i.val + 1 ≤ j.val), xbar s j := by
      have : Finset.univ.filter (fun j : Fin P.N => i.val ≤ j.val) =
          insert i (Finset.univ.filter (fun j : Fin P.N => i.val + 1 ≤ j.val)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro h; by_cases hj : j = i
          · left; exact hj
          · right; have : j.val ≠ i.val := fun e => hj (Fin.ext e); omega
        · rintro (h | h)
          · rw [h]
          · omega
      rw [this, Finset.sum_insert]
      simp
    simp only [H, sofFull]
    rw [hIoi, hIci]
    set R := ∑ j ∈ Finset.univ.filter (fun j : Fin P.N => i.val + 1 ≤ j.val), xbar s j
    omega
  simp_rw [hpt]
  rw [Fin.sum_univ_eq_sum_range (fun k => H k - H (k + 1)), tele H hH]
  have : H 0 ≤ T := min_le_left _ _
  omega

lemma sofFull_shipFeasible {P : Params} (s : State P) (hs : s.Feasible) :
    ShipFeasible s (sofFull s) := by
  refine ⟨fun i => min_le_left _ _, ?_⟩
  have h1 := sofFull_sum_le s
  have h2 : shipTotal s ≤ P.L - ∑ i, s.y i := min_le_left _ _
  have h3 := hs.2.2
  omega

lemma ww_le {P : Params} (hN : 1 ≤ P.N) (s : State P) (hs : s.Feasible) (q : Vec P) :
    ww hN s q ≤ P.SW := by
  unfold ww
  have : xbar s (old P hN) ≤ P.SW := by
    have := xbar_sum_le s hs
    exact le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le (xbar s i))
      (Finset.mem_univ (old P hN))) this
  omega

end PerishShipT1WAux

open PerishShipT1WAux in
theorem solution (P : Params) (hP : P.Standing) :
    ∀ s₀ : State P, s₀.Feasible → ∀ σ : Policy P, σ.Admissible →
      avgUpper (fun s q _ => ww hP.1 s q) (stationary sofFull) s₀ ≤
        avgLower (fun s q _ => ww hP.1 s q) σ s₀ := by
  intro s₀ hs₀ σ hσ
  obtain ⟨C, hC⟩ := sofFull_pathwise_regret P hP
  refine avg_optimal_of_pathwise_regret P.demand next
    (fun s q _ => ((ww hP.1 s q : ℕ) : ENNReal)) sofFull σ s₀ {s | s.Feasible}
    (P.SW : ENNReal) (C : ENNReal) (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _) hs₀
    ?_ ?_ ?_
  · intro s hs ω
    exact next_feasible s _ ω hs (sofFull_shipFeasible s hs)
  · intro s hs _
    exact_mod_cast ww_le hP.1 s hs _
  · intro w x hx u v hu0 hv0 hu hv T
    have hvF : ∀ t, (v t).Feasible := by
      intro t
      induction t with
      | zero => rw [hv0]; exact hs₀
      | succ t ih => rw [hv t]; exact next_feasible _ _ _ ih (hσ t _ ih)
    have key := hC w u v (fun t => σ t (v t)) (by rw [hu0]; exact hx) (by rw [hv0]; exact hs₀)
      hu (fun t => hσ t _ (hvF t)) hv T
    have := (Nat.cast_le (α := ENNReal)).mpr key
    push_cast at this
    exact this
