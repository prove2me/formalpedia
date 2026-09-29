-- Prove2me | solution 1 for TSPHeuristics.KOpt.theorem_6_proof_shortest_even_tour
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:33:38.154885+00:00
-- url     : https://prove2.me/submissions/0f027d00-f6a0-4cf1-91d0-103abb87291d

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance
import Definitions.Def_TSPHeuristics_KOpt_UnitEdgeCount

namespace TSPHeuristics.KOpt

lemma aux_t6_mod (n x y : ℕ) (hx : x < n) (hy : y < n) :
    (x + n - y) % n = if y ≤ x then x - y else x + n - y := by
  split_ifs with h
  · have : x + n - y = (x - y) + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

lemma aux_t6_cycDist_le (n : ℕ) (x y : Fin n) :
    cycDist n x y ≤ ((max x.val y.val - min x.val y.val : ℕ) : ℝ) := by
  unfold cycDist
  rw [aux_t6_mod n x y x.isLt y.isLt, aux_t6_mod n y x y.isLt x.isLt]
  exact Nat.cast_le.mpr (by split_ifs <;> omega)

lemma aux_t6_card_fin (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun e : Fin n => p e.val)).card = ((Finset.range n).filter p).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if p i then 1 else 0) n

lemma aux_t6_cycDist_eq (n : ℕ) (x y : Fin n) :
    cycDist n x y = ((Finset.univ.filter (fun e => arcCovers n x y e)).card : ℝ) := by
  unfold cycDist
  have hx := x.isLt
  have hy := y.isLt
  rw [aux_t6_mod n x y x.isLt y.isLt, aux_t6_mod n y x y.isLt x.isLt]
  congr 1
  by_cases hc : 2 * (max x.val y.val - min x.val y.val) ≤ n
  · have h1 : Finset.univ.filter (fun e => arcCovers n x y e) =
        Finset.univ.filter (fun e : Fin n =>
          min x.val y.val ≤ e.val ∧ e.val < max x.val y.val) :=
      Finset.filter_congr (fun e _ => by unfold arcCovers; rw [if_pos hc])
    rw [h1, aux_t6_card_fin n (fun v => min x.val y.val ≤ v ∧ v < max x.val y.val)]
    have h2 : (Finset.range n).filter (fun v => min x.val y.val ≤ v ∧ v < max x.val y.val) =
        Finset.Ico (min x.val y.val) (max x.val y.val) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [h2, Nat.card_Ico]
    split_ifs <;> omega
  · have h1 : Finset.univ.filter (fun e => arcCovers n x y e) =
        Finset.univ.filter (fun e : Fin n =>
          ¬ (min x.val y.val ≤ e.val ∧ e.val < max x.val y.val)) :=
      Finset.filter_congr (fun e _ => by unfold arcCovers; rw [if_neg hc]; omega)
    rw [h1, aux_t6_card_fin n (fun v => ¬ (min x.val y.val ≤ v ∧ v < max x.val y.val))]
    have h2 : (Finset.range n).filter (fun v => min x.val y.val ≤ v ∧ v < max x.val y.val) =
        Finset.Ico (min x.val y.val) (max x.val y.val) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    have h3 := Finset.card_filter_add_card_filter_not (s := Finset.range n)
      (fun v => min x.val y.val ≤ v ∧ v < max x.val y.val)
    rw [h2, Nat.card_Ico, Finset.card_range] at h3
    split_ifs <;> omega

lemma aux_t6_tour_eq (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    TSPHeuristics.Shared.tourLength (cycDist n) τ = ((∑ e, unitCount τ e : ℕ) : ℝ) := by
  unfold TSPHeuristics.Shared.tourLength unitCount
  simp_rw [aux_t6_cycDist_eq]
  rw [← Nat.cast_sum]
  congr 1
  simp only [Finset.card_filter]
  exact Finset.sum_comm

lemma aux_t6_pt (n : ℕ) (x y e e' : Fin n) (hee : e.val < e'.val) :
    ((if arcCovers n x y e then 1 else 0) + (if arcCovers n x y e' then 1 else 0) +
      (if e.val < x.val ∧ x.val ≤ e'.val then 1 else 0) +
      (if e.val < y.val ∧ y.val ≤ e'.val then 1 else 0) : ℕ) % 2 = 0 := by
  by_cases h1 : arcCovers n x y e <;> by_cases h2 : arcCovers n x y e' <;>
    simp only [h1, h2, if_true, if_false] <;> unfold arcCovers at h1 h2 <;>
    split_ifs at h1 h2 <;> split_ifs <;> omega

lemma aux_t6_parity (n : ℕ) (τ : Equiv.Perm (Fin n)) (e e' : Fin n) (hee : e.val < e'.val) :
    (unitCount τ e + unitCount τ e') % 2 = 0 := by
  set A : Fin n → ℕ := fun v => if e.val < v.val ∧ v.val ≤ e'.val then 1 else 0 with hA
  have hev : Even (∑ k, ((if arcCovers n (τ k) (τ (finRotate n k)) e then 1 else 0) +
      (if arcCovers n (τ k) (τ (finRotate n k)) e' then 1 else 0) + A (τ k) +
      A (τ (finRotate n k)) : ℕ)) :=
    Finset.even_sum _ (fun k _ => Nat.even_iff.mpr (aux_t6_pt n _ _ e e' hee))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hev
  have hrot : ∑ k, A (τ (finRotate n k)) = ∑ k, A (τ k) :=
    Equiv.sum_comp (finRotate n) (fun k => A (τ k))
  rw [hrot] at hev
  unfold unitCount
  rw [Finset.card_filter, Finset.card_filter]
  obtain ⟨r, hr⟩ := hev
  omega

lemma aux_t6_const (n : ℕ) (hn : 0 < n) (P : Fin n → Prop)
    (h : ∀ k, P k ↔ P (finRotate n k)) : ∀ k, P k ↔ P ⟨0, hn⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro ⟨i, hi⟩
  induction i with
  | zero => exact Iff.rfl
  | succ i ih =>
    have h1 := h ⟨i, by omega⟩
    rw [finRotate_of_lt (by omega : i < m)] at h1
    exact h1.symm.trans (ih (by omega))

lemma aux_t6_part1 (n : ℕ) (τ : Equiv.Perm (Fin n)) (e e' : Fin n)
    (he : unitCount τ e = 0) (he' : unitCount τ e' = 0) (hlt : e.val < e'.val) : False := by
  have hn : 0 < n := by have := e.isLt; omega
  have hc : ∀ (f : Fin n), unitCount τ f = 0 → ∀ k, ¬ arcCovers n (τ k) (τ (finRotate n k)) f := by
    intro f hf k hk
    unfold unitCount at hf
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hf
    exact hf (Finset.mem_univ k) hk
  have hP : ∀ k, (e.val < (τ k).val ∧ (τ k).val ≤ e'.val) ↔
      (e.val < (τ (finRotate n k)).val ∧ (τ (finRotate n k)).val ≤ e'.val) := by
    intro k
    have := aux_t6_pt n (τ k) (τ (finRotate n k)) e e' hlt
    simp only [hc e he k, hc e' he' k, if_false] at this
    by_cases ha : e.val < (τ k).val ∧ (τ k).val ≤ e'.val <;>
    by_cases hb : e.val < (τ (finRotate n k)).val ∧ (τ (finRotate n k)).val ≤ e'.val <;>
    simp only [ha, hb, and_self, ite_true, ite_false] at this <;>
    first | exact iff_of_true ha hb | exact iff_of_false ha hb | omega
  have hconst := aux_t6_const n hn (fun k => e.val < (τ k).val ∧ (τ k).val ≤ e'.val) hP
  have hv1 := hconst (τ.symm ⟨e.val + 1, by have := e'.isLt; omega⟩)
  have hv2 := hconst (τ.symm e)
  simp only [Equiv.apply_symm_apply] at hv1 hv2
  have : e.val < e.val + 1 ∧ e.val + 1 ≤ e'.val := ⟨by omega, by omega⟩
  have := hv2.mpr (hv1.mp this)
  omega

lemma aux_t6_lower (n : ℕ) (hn : 0 < n) (c : Fin n → ℕ) (hev : ∀ e, Even (c e))
    (h1 : ∀ e e', c e = 0 → c e' = 0 → e = e') :
    2 * (n - 1) ≤ ∑ e, c e := by
  obtain ⟨e0, he0⟩ : ∃ e0, ∀ e, e ≠ e0 → 2 ≤ c e := by
    by_cases hz : ∃ e, c e = 0
    · obtain ⟨e0, he0⟩ := hz
      refine ⟨e0, fun e he => ?_⟩
      have : c e ≠ 0 := fun h => he (h1 e e0 h he0)
      obtain ⟨r, hr⟩ := hev e
      omega
    · simp only [not_exists] at hz
      refine ⟨⟨0, hn⟩, fun e _ => ?_⟩
      obtain ⟨r, hr⟩ := hev e
      have := hz e
      omega
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
  have : ∑ e ∈ Finset.univ.erase e0, 2 ≤ ∑ e ∈ Finset.univ.erase e0, c e :=
    Finset.sum_le_sum (fun e he => he0 e (Finset.ne_of_mem_erase he))
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at this
  omega

/-- The distance along the line. -/
def aux_t6_δ (n : ℕ) (a b : Fin n) : ℕ := max a.val b.val - min a.val b.val

lemma aux_t6_Q_le (n : ℕ) (z : Fin n) (l : List (Fin n)) : ∀ x : Fin n,
    (List.zipWith (cycDist n) (x :: l) (l ++ [z])).sum ≤
      (((List.zipWith (aux_t6_δ n) (x :: l) (l ++ [z])).sum : ℕ) : ℝ) := by
  induction l with
  | nil => intro x; simpa [aux_t6_δ] using aux_t6_cycDist_le n x z
  | cons w l ih =>
    intro x
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons, Nat.cast_add]
    exact add_le_add (aux_t6_cycDist_le n x w) (ih w)

lemma aux_t6_desc (n : ℕ) (z : Fin n) (l : List (Fin n)) : ∀ w : Fin n,
    List.Pairwise (fun a b : Fin n => b.val ≤ a.val) (w :: l ++ [z]) →
    (List.zipWith (aux_t6_δ n) (w :: l) (l ++ [z])).sum ≤ w.val - z.val ∧ z.val ≤ w.val := by
  induction l with
  | nil =>
    intro w h
    simp [aux_t6_δ] at h ⊢
    omega
  | cons u l ih =>
    intro w h
    simp only [List.cons_append, List.pairwise_cons] at h
    obtain ⟨hw, hrest⟩ := h
    have hu : u.val ≤ w.val := hw u (by simp)
    have ih' := ih u (by simpa [List.pairwise_cons] using hrest)
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
    unfold aux_t6_δ at ih' ⊢
    omega

lemma aux_t6_down (n : ℕ) (x z : Fin n) (l : List (Fin n))
    (h : List.Pairwise (fun a b : Fin n => b.val ≤ a.val) (l ++ [z])) :
    (List.zipWith (aux_t6_δ n) (x :: l) (l ++ [z])).sum ≤ (n - 1 - x.val) + (n - 1 - z.val) := by
  have hx := x.isLt
  have hz := z.isLt
  cases l with
  | nil => simp [aux_t6_δ]; omega
  | cons w l =>
    have hw := w.isLt
    have hd := aux_t6_desc n z l w h
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
    unfold aux_t6_δ at hd ⊢
    omega

lemma aux_t6_up (n : ℕ) (down : List (Fin n)) (z : Fin n)
    (hd : List.Pairwise (fun a b : Fin n => b.val ≤ a.val) (down ++ [z]))
    (up : List (Fin n)) : ∀ x : Fin n,
    List.Pairwise (fun a b : Fin n => a.val ≤ b.val) (x :: up) →
    (List.zipWith (aux_t6_δ n) (x :: (up ++ down)) ((up ++ down) ++ [z])).sum ≤
      (n - 1 - x.val) + (n - 1 - z.val) := by
  induction up with
  | nil => intro x _; simpa using aux_t6_down n x z down hd
  | cons u up ih =>
    intro x h
    rw [List.pairwise_cons] at h
    obtain ⟨hx, hrest⟩ := h
    have hxu : x.val ≤ u.val := hx u (by simp)
    have ih' := ih u hrest
    have := x.isLt
    have := u.isLt
    have := z.isLt
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons] at ih' ⊢
    unfold aux_t6_δ at ih' ⊢
    omega

lemma aux_t6_T (n : ℕ) (hn : 0 < n) :
    circleSubtour n n = ⟨0, hn⟩ :: ((List.finRange n).filter (fun m => m.val < n ∧ Odd m.val) ++
      ((List.finRange n).filter (fun m => m.val < n ∧ m.val ≠ 0 ∧ Even m.val)).reverse) := by
  unfold circleSubtour
  have hA : (List.finRange n).filter (fun m => m.val < n ∧ m.val = 0) = [⟨0, hn⟩] := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [List.finRange_succ]
    simp [List.filter_map]
  rw [hA]
  rfl

lemma aux_t6_cyc_le (n : ℕ) (hn : 0 < n) :
    TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) ≤ ((2 * (n - 1) : ℕ) : ℝ) := by
  rw [aux_t6_T n hn]
  unfold TSPHeuristics.Shared.cycleLength
  rw [List.rotate_cons_succ, List.rotate_zero]
  set B := (List.finRange n).filter (fun m => m.val < n ∧ Odd m.val)
  set C := (List.finRange n).filter (fun m => m.val < n ∧ m.val ≠ 0 ∧ Even m.val)
  refine le_trans (aux_t6_Q_le n ⟨0, hn⟩ (B ++ C.reverse) ⟨0, hn⟩) ?_
  apply Nat.cast_le.mpr
  have hB : List.Pairwise (fun a b : Fin n => a.val ≤ b.val) B :=
    ((List.pairwise_le_finRange n).sublist (List.filter_sublist)).imp (fun h => h)
  have hC : List.Pairwise (fun a b : Fin n => a.val ≤ b.val) C :=
    ((List.pairwise_le_finRange n).sublist (List.filter_sublist)).imp (fun h => h)
  have hd : List.Pairwise (fun a b : Fin n => b.val ≤ a.val) (C.reverse ++ [⟨0, hn⟩]) := by
    rw [List.pairwise_append]
    refine ⟨List.pairwise_reverse.mpr hC, List.pairwise_singleton _ _, ?_⟩
    intro a _ b hb
    simp at hb
    subst hb
    exact Nat.zero_le _
  have hu : List.Pairwise (fun a b : Fin n => a.val ≤ b.val) (⟨0, hn⟩ :: B) :=
    List.pairwise_cons.mpr ⟨fun b _ => Nat.zero_le _, hB⟩
  have := aux_t6_up n C.reverse ⟨0, hn⟩ hd B ⟨0, hn⟩ hu
  simp only at this
  omega

end TSPHeuristics.KOpt

open TSPHeuristics.KOpt

theorem solution (n : ℕ) (hn : 6 ≤ n) :
    (∀ (τ : Equiv.Perm (Fin n)) (e e' : Fin n),
        unitCount τ e = 0 → unitCount τ e' = 0 → e = e') ∧
      (∀ τ : Equiv.Perm (Fin n), (∀ e : Fin n, Even (unitCount τ e)) →
        TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) ≤ TSPHeuristics.Shared.tourLength (cycDist n) τ) ∧
      (∀ τ : Equiv.Perm (Fin n),
        TSPHeuristics.Shared.tourLength (cycDist n) τ < TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) →
          ∀ e : Fin n, Odd (unitCount τ e)) := by
  have hn0 : 0 < n := by omega
  have P1 : ∀ (τ : Equiv.Perm (Fin n)) (e e' : Fin n),
      unitCount τ e = 0 → unitCount τ e' = 0 → e = e' := by
    intro τ e e' he he'
    rcases lt_trichotomy e.val e'.val with h | h | h
    · exact (aux_t6_part1 n τ e e' he he' h).elim
    · exact Fin.ext h
    · exact (aux_t6_part1 n τ e' e he' he h).elim
  have P2 : ∀ τ : Equiv.Perm (Fin n), (∀ e : Fin n, Even (unitCount τ e)) →
      TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n n) ≤
        TSPHeuristics.Shared.tourLength (cycDist n) τ := by
    intro τ hev
    refine le_trans (aux_t6_cyc_le n hn0) ?_
    rw [aux_t6_tour_eq]
    exact Nat.cast_le.mpr (aux_t6_lower n hn0 (unitCount τ) hev (P1 τ))
  refine ⟨P1, P2, ?_⟩
  intro τ hlt e
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hall : ∀ f : Fin n, Even (unitCount τ f) := by
    intro f
    rw [Nat.even_iff] at hodd ⊢
    rcases lt_trichotomy e.val f.val with h | h | h
    · have := aux_t6_parity n τ e f h; omega
    · rw [← Fin.ext h]; exact hodd
    · have := aux_t6_parity n τ f e h; omega
  exact absurd (P2 τ hall) (not_le.mpr hlt)
