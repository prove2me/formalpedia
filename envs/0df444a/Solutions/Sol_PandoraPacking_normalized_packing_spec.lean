-- Prove2me | solution 1 for PandoraPacking.normalized_packing_spec
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:31:57.565506+00:00
-- url     : https://prove2.me/submissions/0047d882-f6d2-4620-8c80-975f27bdfd37

import Definitions.Def_PandoraKnapsack_NormalizedPacking

namespace PandoraPacking
noncomputable section

theorem update_cube {d : ℕ} (a x : Vec d) : Cube (update a x) := by
  intro j
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private theorem clip_dist (v y : ℝ) (hy : 0 ≤ y ∧ y ≤ 1) :
    (clip v - y)^2 ≤ (v-y)^2 := by
  unfold clip
  rcases le_total v 0 with hv | hv
  · rw [min_eq_right (by linarith), max_eq_left hv]
    nlinarith [mul_nonneg (neg_nonneg.mpr hv) (sub_nonneg.mpr (show v ≤ 2*y by linarith [hy.1]))]
  · rcases le_total v 1 with hv' | hv'
    · rw [min_eq_right hv', max_eq_right hv]
    · rw [min_eq_left hv', max_eq_right zero_le_one]
      nlinarith [mul_nonneg (sub_nonneg.mpr hv') (sub_nonneg.mpr (show 2*y ≤ v+1 by linarith [hy.2]))]

theorem potential_nonneg {d : ℕ} (x y : Vec d) : 0 ≤ potential x y := by
  unfold potential energy
  positivity

theorem potential_initial {d : ℕ} {y : Vec d} (hy : Cube y) :
    potential 0 y ≤ 64 * ((d+1 : ℕ) : ℝ)^2 := by
  have h : energy 0 y ≤ d := calc
    _ ≤ ∑ _j : Fin d, (1:ℝ) := Finset.sum_le_sum fun j _ => by
      change ((0:ℝ) - y j)^2 ≤ 1
      nlinarith [mul_nonneg (sub_nonneg.mpr (hy j).2) (show 0 ≤ y j + 1 by linarith [(hy j).1])]
    _ = d := by simp
  unfold potential
  push_cast at *
  nlinarith [mul_le_mul_of_nonneg_left h (show 0 ≤ 64*((d:ℝ)+1) by positivity)]

/-- A row separating the current point from a cube witness by more than one eighth
pays for one full unit of the scaled potential. -/
theorem potential_drop {d : ℕ} {a x y : Vec d} (hy : Cube y)
    (ha : ∀ j, -1 ≤ a j ∧ a j ≤ 1) (hgap : dot a y + 1/8 < dot a x) :
    potential (update a x) y + 1 ≤ potential x y := by
  have hc : energy (update a x) y ≤ ∑ j, ((x j - rate d * a j) - y j)^2 :=
    Finset.sum_le_sum fun j _ => clip_dist _ _ (hy j)
  have he : (∑ j, ((x j - rate d * a j) - y j)^2) =
      energy x y - 2 * rate d * (dot a x - dot a y) + (rate d)^2 * ∑ j, (a j)^2 := by
    unfold energy dot
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hn : (∑ j, (a j)^2) ≤ (d:ℝ) := calc
    _ ≤ ∑ _j : Fin d, (1:ℝ) := Finset.sum_le_sum fun j _ => by
      nlinarith [mul_nonneg (show 0 ≤ 1+a j by linarith [(ha j).1]) (sub_nonneg.mpr (ha j).2)]
    _ = d := by simp
  have hpos : 0 < rate d := by unfold rate; positivity
  have hrate : rate d * (8*((d+1:ℕ):ℝ)) = 1 := by
    unfold rate
    field_simp
  rw [he] at hc
  have hv := mul_le_mul_of_nonneg_left hn (sq_nonneg (rate d))
  have hg := mul_le_mul_of_nonneg_left (show 1/8 ≤ dot a x - dot a y by linarith) (show 0 ≤ 2 * rate d by positivity)
  have hh : rate d * ((d+1:ℕ):ℝ) = 1/8 := by linarith
  have hh2 := congrArg (fun q : ℝ => rate d * q) hh
  change rate d * (rate d * ((d+1:ℕ):ℝ)) = rate d * (1/8) at hh2
  have hde : energy (update a x) y + rate d / 8 ≤ energy x y := by
    push_cast at hh2
    nlinarith [sq_nonneg (rate d)]
  unfold potential
  have hd := mul_le_mul_of_nonneg_left hde (show 0 ≤ 64*((d+1:ℕ):ℝ) by positivity)
  linarith

theorem iterate_success {d : ℕ} (rows : List (Row d)) (fuel : ℕ) (x y : Vec d)
    (hy : Cube y) (hn : ∀ q ∈ rows, ∀ j, -1 ≤ q.coeff j ∧ q.coeff j ≤ 1)
    (hs : ∀ q ∈ rows, dot q.coeff y ≤ q.bound) (hf : potential x y < fuel) :
    ∃ z, iterate rows fuel x = some z := by
  induction fuel generalizing x with
  | zero => simp only [Nat.cast_zero] at hf; linarith [potential_nonneg x y]
  | succ fuel ih =>
    rw [iterate]
    cases hr : badRow rows x with
    | none => exact ⟨_,rfl⟩
    | some q =>
      have hm := List.mem_of_find?_eq_some hr
      have hv0 := List.find?_some (p := fun q : Row d => decide (q.bound + 1/8 < dot q.coeff x)) hr
      have hv : q.bound + 1/8 < dot q.coeff x := by simpa using hv0
      have hsep : dot q.coeff y + 1/8 < dot q.coeff x := by linarith [hs q hm]
      have hdrop := potential_drop hy (hn q hm) hsep
      exact ih _ (by push_cast at hf; linarith)

theorem iterate_sound {d : ℕ} (rows : List (Row d)) (fuel : ℕ) {x z : Vec d}
    (hx : Cube x) (hr : iterate rows fuel x = some z) :
    Cube z ∧ ∀ q ∈ rows, dot q.coeff z ≤ q.bound + 1/8 := by
  induction fuel generalizing x with
  | zero => simp [iterate] at hr
  | succ fuel ih =>
    simp only [iterate] at hr
    cases hd : badRow rows x with
    | some q =>
      rw [hd] at hr
      exact ih (update_cube _ _) hr
    | none =>
      rw [hd] at hr
      cases hr
      refine ⟨hx, fun q hm => ?_⟩
      exact le_of_not_gt (by simpa using List.find?_eq_none.mp hd q hm)

theorem zero_feasible {r d : ℕ} (A : Matrix r d) : Feasible A 0 := by
  constructor
  · intro j
    simp
  · intro i
    simp [dot]

private theorem dot_scale {d : ℕ} (a x : Vec d) : dot a (scale x) = (8/9) * dot a x := by
  unfold dot scale
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem dot_neg {d : ℕ} (c y : Vec d) : dot (fun j => -(c j)) y = -(dot c y) := by
  simp [dot, Finset.sum_neg_distrib]

private theorem mem_row {r d : ℕ} (A : Matrix r d) (c : Vec d) (g : ℝ) (i : Fin r) :
    (⟨A i, 1⟩ : Row d) ∈ rowsFor A c g := by
  unfold rowsFor
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩)

private theorem first_row {r d : ℕ} (A : Matrix r d) (c : Vec d) (g : ℝ) :
    (⟨fun j => -(c j), -g⟩ : Row d) ∈ rowsFor A c g := List.mem_cons_self

private theorem trial_feasible {r d : ℕ} (A : Matrix r d) (c : Vec d) (k : ℕ) :
    Feasible A (trial A c k) := by
  unfold trial
  cases ht : iterate _ _ _ with
  | none => exact zero_feasible _
  | some x =>
    obtain ⟨hx,hr⟩ := iterate_sound _ _ (zero_feasible A).1 ht
    constructor
    · intro j
      change 0 ≤ 8/9 * x j ∧ 8/9 * x j ≤ 1
      constructor <;> linarith [(hx j).1, (hx j).2]
    · intro i
      have h := hr _ (mem_row A c _ i)
      change dot (A i) x ≤ 1+1/8 at h
      rw [dot_scale]
      linarith

theorem search_feasible {r d : ℕ} (A : Matrix r d) (c : Vec d) (k : ℕ) :
    Feasible A (search A c k) := by
  induction k with
  | zero => exact zero_feasible A
  | succ k ih =>
    unfold search better
    split
    · exact trial_feasible A c k
    · exact ih

private theorem trial_le_search {r d : ℕ} (A : Matrix r d) (c : Vec d) {k K : ℕ} (hk : k < K) :
    dot c (trial A c k) ≤ dot c (search A c K) := by
  induction K with
  | zero => omega
  | succ K ih =>
    by_cases h : k = K
    · subst k
      unfold search better
      split
      · exact le_rfl
      · exact le_of_not_gt (by assumption)
    · have h' := ih (by omega)
      unfold search better
      split
      · exact h'.trans (le_of_lt (by assumption))
      · exact h'

private theorem trial_value {r d : ℕ} (A : Matrix r d) (c y : Vec d)
    (ha : ∀ i, Cube (A i)) (hc : Cube c) (hy : Feasible A y)
    (k : ℕ) (hg : (k:ℝ)/8 ≤ dot c y) :
    (8/9)*((k:ℝ)/8 - 1/8) ≤ dot c (trial A c k) := by
  let rows := rowsFor A c ((k:ℝ)/8)
  have normRows : ∀ q ∈ rows, ∀ j, -1 ≤ q.coeff j ∧ q.coeff j ≤ 1 := by
    intro q hm j
    rcases List.mem_cons.mp hm with he | hm
    · subst q
      change -1 ≤ -c j ∧ -c j ≤ 1
      constructor <;> linarith [(hc j).1, (hc j).2]
    · obtain ⟨i,_,he⟩ := List.mem_map.mp hm
      subst q
      change -1 ≤ A i j ∧ A i j ≤ 1
      exact ⟨by linarith [(ha i j).1],(ha i j).2⟩
  have wit : ∀ q ∈ rows, dot q.coeff y ≤ q.bound := by
    intro q hm
    rcases List.mem_cons.mp hm with he | hm
    · subst q
      change dot (fun j => -c j) y ≤ -((k:ℝ)/8)
      simpa only [dot_neg, neg_le_neg_iff] using hg
    · obtain ⟨i,_,he⟩ := List.mem_map.mp hm
      subst q
      exact hy.2 i
  have hf : potential 0 y < fuelBound d := by
    have h := potential_initial hy.1
    unfold fuelBound
    push_cast at *
    linarith
  obtain ⟨z,hz⟩ := iterate_success rows (fuelBound d) 0 y hy.1 normRows wit hf
  obtain ⟨_,hh⟩ := iterate_sound rows _ (zero_feasible A).1 hz
  have hv := hh _ (first_row A c _)
  change dot (fun j => -c j) z ≤ -((k:ℝ)/8) + 1/8 at hv
  rw [dot_neg] at hv
  unfold trial
  rw [show iterate (rowsFor A c ((k:ℝ)/8)) (fuelBound d) 0 = some z from hz]
  change _ ≤ dot c (scale z)
  rw [dot_scale]
  linarith

/-- For every feasible point earning at least one normalized unit, the finite search
earns at least two thirds of its profit. -/
theorem solve_value {r d : ℕ} (A : Matrix r d) (c y : Vec d)
    (ha : ∀ i, Cube (A i)) (hc : Cube c) (hy : Feasible A y) (h1 : 1 ≤ dot c y) :
    (2/3) * dot c y ≤ dot c (solve A c) := by
  have hv : dot c y ≤ d := calc
    _ ≤ ∑ _j : Fin d, (1:ℝ) := Finset.sum_le_sum fun j _ =>
      mul_le_one₀ (hc j).2 (hy.1 j).1 (hy.1 j).2
    _ = d := by simp
  let k : ℕ := ⌊8 * dot c y⌋₊
  have hg : (k:ℝ)/8 ≤ dot c y := by
    have hf := Nat.floor_le (show 0 ≤ 8*dot c y by linarith)
    dsimp [k]
    linarith
  have hk : k ≤ 8*d := by
    apply Nat.floor_le_of_le
    push_cast
    linarith
  have ht := trial_value A c y ha hc hy k hg
  have hs := trial_le_search A c (show k < 8*d+1 by omega)
  have near := Nat.lt_floor_add_one (8 * dot c y)
  change 8 * dot c y < (k:ℝ)+1 at near
  unfold solve
  linarith

theorem solve_feasible {r d : ℕ} (A : Matrix r d) (c : Vec d) : Feasible A (solve A c) :=
  search_feasible A c _

/-- The anchor witnesses the normalization of the optimum. -/
theorem solve_half {r d : ℕ} (A : Matrix r d) (c : Vec d)
    (ha : ∀ i, Cube (A i)) (hc : Cube c)
    (anchor : Vec d) (haF : Feasible A anchor) (ha1 : 1 ≤ dot c anchor) :
    Feasible A (solve A c) ∧ ∀ y, Feasible A y → dot c y ≤ 2 * dot c (solve A c) := by
  refine ⟨solve_feasible A c, fun y hy => ?_⟩
  by_cases h1 : 1 ≤ dot c y
  · linarith [solve_value A c y ha hc hy h1]
  · linarith [solve_value A c anchor ha hc haF ha1]

end
end PandoraPacking

open PandoraPacking

theorem solution {r d : ℕ} (A : Matrix r d) (c : Vec d) :
    Feasible A (solve A c) ∧
    ((∀ i, Cube (A i)) → Cube c → ∀ anchor, Feasible A anchor → 1 ≤ dot c anchor →
        ∀ y, Feasible A y → dot c y ≤ 2 * dot c (solve A c)) := by
  exact ⟨solve_feasible A c, fun ha hc anchor hf hv => (solve_half A c ha hc anchor hf hv).2⟩
