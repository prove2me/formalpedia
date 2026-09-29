-- Prove2me | solution 1 for TSPHeuristics.KOpt.theorem_5_proof_circle_run_nearest_cheapest
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:46:32.107199+00:00
-- url     : https://prove2.me/submissions/998df6c2-a27a-45d4-8633-a6e9d4104e0a

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion
import Definitions.Def_TSPHeuristics_KOpt_CircleInstance

namespace TSPHeuristics.KOpt
noncomputable def aux_c5_cl {α : Type} (d : α → α → ℝ) (L : List α) : ℝ :=
  (List.zipWith d L (L.rotate 1)).sum

noncomputable def aux_c5_pl {α : Type} (d : α → α → ℝ) : List α → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: l => d a b + aux_c5_pl d (b :: l)

theorem aux_c5_cl_rotate {α : Type} (d : α → α → ℝ) (L : List α) (k : ℕ) :
    aux_c5_cl d (L.rotate k) = aux_c5_cl d L := by
  unfold aux_c5_cl
  rw [List.rotate_rotate, Nat.add_comm k 1, ← List.rotate_rotate,
    ← List.zipWith_rotate_distrib _ _ _ _ (by simp)]
  exact (List.rotate_perm _ _).sum_eq

theorem aux_c5_cl_swap {α : Type} (d : α → α → ℝ) (A B : List α) :
    aux_c5_cl d (A ++ B) = aux_c5_cl d (B ++ A) := by
  rw [← List.rotate_append_length_eq A B, aux_c5_cl_rotate]

theorem aux_c5_K {α : Type} (d : α → α → ℝ) (R : List α) :
    ∀ (v u y : α), (v :: R).getLast? = some u →
      (List.zipWith d (v :: R) (R ++ [y])).sum = aux_c5_pl d (v :: R) + d u y := by
  induction R with
  | nil =>
    intro v u y h
    simp at h
    subst h
    simp [aux_c5_pl]
  | cons r R ih =>
    intro v u y h
    have h' : (r :: R).getLast? = some u := by
      rw [List.getLast?_cons_cons] at h; exact h
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
    rw [ih r u y h', aux_c5_pl]
    ring

theorem aux_c5_P {α : Type} (d : α → α → ℝ) (R : List α) :
    ∀ (v u x : α), (v :: R).getLast? = some u →
      aux_c5_pl d (v :: (R ++ [x])) = aux_c5_pl d (v :: R) + d u x := by
  induction R with
  | nil =>
    intro v u x h
    simp at h
    subst h
    simp [aux_c5_pl]
  | cons r R ih =>
    intro v u x h
    have h' : (r :: R).getLast? = some u := by
      rw [List.getLast?_cons_cons] at h; exact h
    simp only [List.cons_append]
    rw [aux_c5_pl, aux_c5_pl, ih r u x h']
    ring

theorem aux_c5_cl_cons {α : Type} (d : α → α → ℝ) (v : α) (R : List α) :
    aux_c5_cl d (v :: R) = (List.zipWith d (v :: R) (R ++ [v])).sum := by
  unfold aux_c5_cl
  rw [show (1:ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]

theorem aux_c5_J {α : Type} (d : α → α → ℝ) (L : List α) (x u v : α)
    (hu : L.getLast? = some u) (hv : L.head? = some v) :
    aux_c5_cl d (L ++ [x]) = aux_c5_cl d L + d u x + d x v - d u v := by
  cases L with
  | nil => simp at hu
  | cons w R =>
    simp at hv
    subst hv
    rw [List.cons_append, aux_c5_cl_cons, aux_c5_cl_cons,
      aux_c5_K d (R ++ [x]) w x w (by rw [← List.cons_append, List.getLast?_concat]), aux_c5_K d R w u w hu, aux_c5_P d R w u x hu]
    ring

theorem aux_c5_junction {α : Type} (d : α → α → ℝ) (A B : List α) (x u v : α)
    (hu : (B ++ A).getLast? = some u) (hv : (B ++ A).head? = some v) :
    aux_c5_cl d (A ++ x :: B) = aux_c5_cl d (A ++ B) + d u x + d x v - d u v := by
  rw [aux_c5_cl_swap, show x :: B ++ A = [x] ++ (B ++ A) by simp, aux_c5_cl_swap,
    aux_c5_J d _ x u v hu hv, aux_c5_cl_swap d B A]

theorem aux_c5_decomp {α : Type} (x : α) :
    ∀ (pos : ℕ) (L : List α), pos ≤ L.length →
      ∃ A B, L = A ++ B ∧ L.insertIdx pos x = A ++ x :: B := by
  intro pos
  induction pos with
  | zero => intro L _; exact ⟨[], L, by simp, by simp⟩
  | succ p ih =>
    intro L hL
    cases L with
    | nil => simp at hL
    | cons a L =>
      obtain ⟨A, B, h1, h2⟩ := ih L (by simpa using hL)
      refine ⟨a :: A, B, by simp [h1], ?_⟩
      rw [List.insertIdx_succ_cons, h2]
      simp

theorem aux_c5_insert_len {α : Type} (x : α) (A B : List α) :
    (A ++ B).insertIdx A.length x = A ++ x :: B := by
  induction A with
  | nil => simp
  | cons a A ih => simp only [List.cons_append, List.length_cons]; rw [List.insertIdx_succ_cons, ih]

theorem aux_c5_LB {α : Type} (d : α → α → ℝ) (P : α → α → Prop) (T : List α) (x : α) (c : ℝ)
    (hne : T ≠ []) (hch : T.IsChain P) (hw : ∀ u ∈ T.getLast?, ∀ v ∈ T.head?, P u v)
    (hc : ∀ u ∈ T, ∀ v ∈ T, P u v → c ≤ d u x + d x v - d u v) (pos : ℕ) (hpos : pos ≤ T.length) :
    aux_c5_cl d T + c ≤ aux_c5_cl d (T.insertIdx pos x) := by
  obtain ⟨A, B, h1, h2⟩ := aux_c5_decomp x pos T hpos
  have hBA : B ++ A ≠ [] := by
    intro h; apply hne; rw [h1]; simp at h ⊢; exact ⟨h.2, h.1⟩
  obtain ⟨u, hu⟩ : ∃ u, (B ++ A).getLast? = some u :=
    Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hBA)
  obtain ⟨v, hv⟩ : ∃ v, (B ++ A).head? = some v :=
    Option.isSome_iff_exists.mp (List.isSome_head?.mpr hBA)
  rw [h2, aux_c5_junction d A B x u v hu hv, ← h1]
  have huT : u ∈ T := by
    have := List.mem_of_getLast? hu; rw [h1]; simp at this ⊢; tauto
  have hvT : v ∈ T := by
    have := List.mem_of_mem_head? hv; rw [h1]; simp at this ⊢; tauto
  have hP : P u v := by
    rcases A.eq_nil_or_concat with hA | ⟨A', a, hA⟩
    · subst hA; simp at hu hv h1; subst h1; exact hw u (by simp [hu]) v (by simp [hv])
    rcases B with _ | ⟨b, B'⟩
    · simp at hu hv h1; subst h1; exact hw u (by simp [hu]) v (by simp [hv])
    · subst hA
      rw [List.concat_eq_append, ← List.append_assoc, List.getLast?_concat] at hu
      simp at hu hv
      subst hu; subst hv
      rw [h1] at hch
      exact (List.isChain_append.mp hch).2.2 _ (by simp) _ (by simp)
  have := hc u huT v hvT hP
  linarith

def aux_c5_Dn (n a b : ℕ) : ℕ := min ((a + n - b) % n) ((b + n - a) % n)

theorem aux_c5_mod (n a b : ℕ) (ha : a < n) (hb : b < n) :
    (a + n - b) % n = if b ≤ a then a - b else a + n - b := by
  split_ifs with h
  · rw [show a + n - b = (a - b) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

theorem aux_c5_Dn_eq (n a b : ℕ) (ha : a < n) (hb : b < n) :
    aux_c5_Dn n a b = min (if b ≤ a then a - b else a + n - b) (if a ≤ b then b - a else b + n - a) := by
  unfold aux_c5_Dn; rw [aux_c5_mod n a b ha hb, aux_c5_mod n b a hb ha]

def aux_c5_O (i : ℕ) : List ℕ := (List.range (i/2)).map (fun j => 2*j+1)
def aux_c5_E (i : ℕ) : List ℕ := ((List.range ((i-1)/2)).map (fun j => 2*j+2)).reverse
def aux_c5_S (i : ℕ) : List ℕ := 0 :: (aux_c5_O i ++ aux_c5_E i)

theorem aux_c5_mf (n : ℕ) (p : ℕ → Bool) :
    ((List.finRange n).filter (fun m => p m.val)).map Fin.val = (List.range n).filter p := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map]; rfl

theorem aux_c5_restrict (n i : ℕ) (hi : i ≤ n) (p : ℕ → Prop) [DecidablePred p] :
    (List.range n).filter (fun m => m < i ∧ p m) = (List.range i).filter p := by
  rw [show n = i + (n - i) by omega, List.range_add, List.filter_append]
  have h1 : (List.map (fun x => i + x) (List.range (n - i))).filter (fun m => m < i ∧ p m) = [] := by
    rw [List.filter_eq_nil_iff]; intro a ha; simp at ha ⊢; obtain ⟨b, _, rfl⟩ := ha; omega
  rw [h1, List.append_nil]
  apply List.filter_congr
  intro m hm; simp at hm; simp [hm]

theorem aux_c5_f0 (i : ℕ) (hi : 1 ≤ i) : (List.range i).filter (fun m => m = 0) = [0] := by
  induction i with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; decide
    · rw [List.range_succ, List.filter_append, ih h]; simp; omega

theorem aux_c5_f1 (i : ℕ) : (List.range i).filter (fun m => Odd m) = aux_c5_O i := by
  induction i with
  | zero => simp [aux_c5_O]
  | succ k ih =>
    rw [List.range_succ, List.filter_append, ih]
    unfold aux_c5_O
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · subst hj
      rw [show (j + j + 1) / 2 = (j + j) / 2 by omega]
      have : ¬ Odd (j + j) := by rw [Nat.not_odd_iff_even]; exact ⟨j, rfl⟩
      simp [this]
    · subst hj
      rw [show (2 * j + 1 + 1) / 2 = (2 * j + 1) / 2 + 1 by omega, List.range_succ, List.map_append]
      have : Odd (2 * j + 1) := ⟨j, rfl⟩
      simp [this]
      omega

theorem aux_c5_f2 (i : ℕ) :
    (List.range i).filter (fun m => m ≠ 0 ∧ Even m) = (List.range ((i-1)/2)).map (fun j => 2*j+2) := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.filter_append, ih]
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · subst hj
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; simp
      · rw [show (j + j + 1 - 1) / 2 = (j + j - 1) / 2 + 1 by omega, List.range_succ, List.map_append]
        have : Even (j + j) := ⟨j, rfl⟩
        have h2 : j ≠ 0 := by omega
        rw [List.map_singleton, show 2 * ((j + j - 1) / 2) + 2 = j + j by omega]
        simp [List.filter_cons, this, h2]
    · subst hj
      rw [show (2 * j + 1 + 1 - 1) / 2 = (2 * j + 1 - 1) / 2 by omega]
      have : ¬ Even (2 * j + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨j, rfl⟩
      simp [this]

theorem aux_c5_mapS (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    (circleSubtour n i).map Fin.val = aux_c5_S i := by
  unfold circleSubtour
  rw [List.map_append, List.map_append, List.map_reverse]
  rw [aux_c5_mf n (fun m => decide (m < i ∧ m = 0)), aux_c5_mf n (fun m => decide (m < i ∧ Odd m)),
    aux_c5_mf n (fun m => decide (m < i ∧ m ≠ 0 ∧ Even m))]
  rw [aux_c5_restrict n i hin (fun m => m = 0), aux_c5_restrict n i hin (fun m => Odd m),
    aux_c5_restrict n i hin (fun m => m ≠ 0 ∧ Even m)]
  rw [aux_c5_f0 i hi, aux_c5_f1, aux_c5_f2]
  simp [aux_c5_S, aux_c5_E]


theorem aux_c5_S_len (i : ℕ) (hi : 1 ≤ i) : (aux_c5_S i).length = i := by
  simp [aux_c5_S, aux_c5_O, aux_c5_E]; omega

theorem aux_c5_S_mem (i u : ℕ) (hu : u ∈ aux_c5_S i) (hi : 1 ≤ i) : u < i := by
  simp [aux_c5_S, aux_c5_O, aux_c5_E] at hu
  rcases hu with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> omega

theorem aux_c5_S_chain (i : ℕ) : (aux_c5_S i).IsChain (fun a b => a ≤ b + 2 ∧ b ≤ a + 2) := by
  unfold aux_c5_S
  rw [List.isChain_cons]
  constructor
  · intro y hy
    simp [aux_c5_O, aux_c5_E, List.head?_range, List.getLast?_range] at hy
    omega
  · apply List.IsChain.append
    · unfold aux_c5_O
      rw [List.isChain_map, List.isChain_range]
      intro m _; omega
    · unfold aux_c5_E
      rw [List.isChain_reverse, List.isChain_map, List.isChain_range]
      intro m _; omega
    · intro x hx y hy
      simp [aux_c5_O, aux_c5_E, List.head?_range, List.getLast?_range] at hx hy
      omega

theorem aux_c5_S_wrap (i : ℕ) :
    ∀ u ∈ (aux_c5_S i).getLast?, ∀ v ∈ (aux_c5_S i).head?, u ≤ v + 2 ∧ v ≤ u + 2 := by
  intro u hu v hv
  simp [aux_c5_S] at hv
  subst hv
  simp [aux_c5_S, List.getLast?_cons, aux_c5_O, aux_c5_E, List.head?_range, List.getLast?_range] at hu
  split_ifs at hu <;> simp at hu <;> omega

theorem aux_c5_S_split (i : ℕ) : aux_c5_S i = (0 :: aux_c5_O i) ++ aux_c5_E i := by
  simp [aux_c5_S]

theorem aux_c5_S_step (i : ℕ) (hi : 1 ≤ i) :
    aux_c5_S (i + 1) = (0 :: aux_c5_O i) ++ i :: aux_c5_E i := by
  unfold aux_c5_S aux_c5_O aux_c5_E
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    rw [show (j + j + 1) / 2 = (j + j) / 2 by omega,
      show (j + j + 1 - 1) / 2 = (j + j - 1) / 2 + 1 by omega, List.range_succ, List.map_append,
      List.reverse_append]
    simp
    omega
  · subst hj
    rw [show (2 * j + 1 + 1) / 2 = (2 * j + 1) / 2 + 1 by omega,
      show (2 * j + 1 + 1 - 1) / 2 = (2 * j + 1 - 1) / 2 by omega, List.range_succ, List.map_append]
    simp
    omega

theorem aux_c5_Dn_ord (n a b : ℕ) (hab : a ≤ b) (hb : b < n) :
    aux_c5_Dn n a b = min (b - a) (n - (b - a)) ∧ aux_c5_Dn n b a = min (b - a) (n - (b - a)) := by
  unfold aux_c5_Dn
  rw [aux_c5_mod n a b (by omega) hb, aux_c5_mod n b a hb (by omega)]
  constructor <;> split_ifs <;> omega

theorem aux_c5_Dn_lin (n a b : ℕ) (hab : a ≤ b) (hb : b < n) (h : 2 * (b - a) ≤ n) :
    aux_c5_Dn n a b = b - a ∧ aux_c5_Dn n b a = b - a := by
  obtain ⟨h1, h2⟩ := aux_c5_Dn_ord n a b hab hb
  rw [h1, h2]; omega

theorem aux_c5_junc_last (i : ℕ) (u : ℕ)
    (hu : (aux_c5_E i ++ 0 :: aux_c5_O i).getLast? = some u) :
    u = if i / 2 = 0 then 0 else 2 * (i / 2) - 1 := by
  rw [List.getLast?_append, List.getLast?_cons, Option.some_or] at hu
  unfold aux_c5_O at hu
  rw [List.getLast?_map, List.getLast?_range] at hu
  by_cases h : i / 2 = 0
  · rw [if_pos h] at hu ⊢; simp at hu; omega
  · rw [if_neg h] at hu ⊢; simp at hu; omega

theorem aux_c5_junc_head (i : ℕ) (v : ℕ)
    (hv : (aux_c5_E i ++ 0 :: aux_c5_O i).head? = some v) :
    v = if (i - 1) / 2 = 0 then 0 else 2 * ((i - 1) / 2) := by
  rw [List.head?_append] at hv
  unfold aux_c5_E at hv
  rw [List.head?_reverse, List.getLast?_map, List.getLast?_range] at hv
  by_cases h : (i - 1) / 2 = 0
  · rw [if_pos h] at hv ⊢; simp at hv; omega
  · rw [if_neg h] at hv ⊢; simp at hv; omega

theorem aux_c5_S_junc (n i : ℕ) (hn : 6 ≤ n) (hi : 1 ≤ i) (hin : i < n) (u v : ℕ)
    (hu : (aux_c5_E i ++ 0 :: aux_c5_O i).getLast? = some u)
    (hv : (aux_c5_E i ++ 0 :: aux_c5_O i).head? = some v) :
    aux_c5_Dn n u i + aux_c5_Dn n i v = aux_c5_Dn n u v + 2 := by
  have hu' := aux_c5_junc_last i u hu
  have hv' := aux_c5_junc_head i v hv
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · interval_cases i
    · simp at hu' hv'; subst hu' hv'
      rw [(aux_c5_Dn_lin n 0 1 (by omega) (by omega) (by omega)).1,
        (aux_c5_Dn_lin n 0 1 (by omega) (by omega) (by omega)).2,
        (aux_c5_Dn_lin n 0 0 (by omega) (by omega) (by omega)).1]
    · simp at hu' hv'; subst hu' hv'
      rw [(aux_c5_Dn_lin n 1 2 (by omega) (by omega) (by omega)).1,
        (aux_c5_Dn_lin n 0 2 (by omega) (by omega) (by omega)).2,
        (aux_c5_Dn_lin n 0 1 (by omega) (by omega) (by omega)).2]
  · rw [if_neg (show ¬ i / 2 = 0 by omega)] at hu'
    rw [if_neg (show ¬ (i - 1) / 2 = 0 by omega)] at hv'
    rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
    · have e1 : u = i - 1 := by omega
      have e2 : v = i - 2 := by omega
      subst e1 e2
      rw [(aux_c5_Dn_lin n (i - 1) i (by omega) (by omega) (by omega)).1,
        (aux_c5_Dn_lin n (i - 2) i (by omega) (by omega) (by omega)).2,
        (aux_c5_Dn_lin n (i - 2) (i - 1) (by omega) (by omega) (by omega)).2]
      omega
    · have e1 : u = i - 2 := by omega
      have e2 : v = i - 1 := by omega
      subst e1 e2
      rw [(aux_c5_Dn_lin n (i - 2) i (by omega) (by omega) (by omega)).1,
        (aux_c5_Dn_lin n (i - 1) i (by omega) (by omega) (by omega)).2,
        (aux_c5_Dn_lin n (i - 2) (i - 1) (by omega) (by omega) (by omega)).1]
      omega

theorem aux_c5_clmap (n : ℕ) (T : List (Fin n)) :
    TSPHeuristics.Shared.cycleLength (cycDist n) T =
      aux_c5_cl (fun a b => ((aux_c5_Dn n a b : ℕ) : ℝ)) (T.map Fin.val) := by
  unfold TSPHeuristics.Shared.cycleLength aux_c5_cl
  rw [← List.map_rotate, List.zipWith_map]; rfl

theorem aux_c5_node (n : ℕ) (h : 0 < n) (i : ℕ) (hi : i < n) : circleNode n h i = ⟨i, hi⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hi)

theorem aux_c5_memT (n i : ℕ) (m : Fin n) : m ∈ circleSubtour n i ↔ m.val < i := by
  unfold circleSubtour
  simp only [List.mem_append, List.mem_filter, List.mem_reverse, List.mem_finRange, true_and,
    decide_eq_true_eq]
  constructor
  · rintro ((h | h) | h) <;> exact h.1
  · intro h
    rcases Nat.even_or_odd m.val with he | ho
    · by_cases h0 : m.val = 0
      · exact Or.inl (Or.inl ⟨h, h0⟩)
      · exact Or.inr ⟨h, h0, he⟩
    · exact Or.inl (Or.inr ⟨h, ho⟩)

theorem aux_c5_lenT (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) : (circleSubtour n i).length = i := by
  rw [← List.length_map (f := Fin.val), aux_c5_mapS n i hi hin, aux_c5_S_len i hi]

theorem aux_c5_LBF (n i : ℕ) (hn : 6 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) (x : Fin n) (hx : i ≤ x.val)
    (pos : ℕ) (hpos : pos ≤ (circleSubtour n i).length) :
    TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n i) + 2 ≤
      TSPHeuristics.Shared.cycleLength (cycDist n) ((circleSubtour n i).insertIdx pos x) := by
  rw [aux_c5_clmap, aux_c5_clmap, List.map_insertIdx, aux_c5_mapS n i hi hin]
  apply aux_c5_LB _ (fun a b => a ≤ b + 2 ∧ b ≤ a + 2) (aux_c5_S i) x.val 2 (by simp [aux_c5_S])
    (aux_c5_S_chain i) (aux_c5_S_wrap i)
  · intro u hu v hv hP
    have hu' := aux_c5_S_mem i u hu hi
    have hv' := aux_c5_S_mem i v hv hi
    have hxn := x.isLt
    have key : aux_c5_Dn n u v + 2 ≤ aux_c5_Dn n u x.val + aux_c5_Dn n x.val v := by
      obtain ⟨hP1, hP2⟩ := hP
      obtain ⟨e3, -⟩ := aux_c5_Dn_ord n u x.val (by omega) hxn
      obtain ⟨-, e6⟩ := aux_c5_Dn_ord n v x.val (by omega) hxn
      rw [e3, e6]
      rcases le_total u v with huv | huv
      · rw [(aux_c5_Dn_ord n u v huv (by omega)).1]; omega
      · rw [(aux_c5_Dn_ord n v u huv (by omega)).2]; omega
    have := (Nat.cast_le (α := ℝ)).mpr key
    push_cast at this
    linarith
  · rw [aux_c5_S_len i hi]; rw [aux_c5_lenT n i hi hin] at hpos; exact hpos

theorem aux_c5_EXF (n i : ℕ) (hn : 6 ≤ n) (hi : 1 ≤ i) (hin : i < n) :
    TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n (i + 1)) =
      TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n i) + 2 := by
  rw [aux_c5_clmap, aux_c5_clmap, aux_c5_mapS n (i + 1) (by omega) (by omega),
    aux_c5_mapS n i hi (by omega), aux_c5_S_step i hi, aux_c5_S_split i]
  have hne : aux_c5_E i ++ 0 :: aux_c5_O i ≠ [] := by simp
  obtain ⟨u, hu⟩ : ∃ u, (aux_c5_E i ++ 0 :: aux_c5_O i).getLast? = some u :=
    Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne)
  obtain ⟨v, hv⟩ : ∃ v, (aux_c5_E i ++ 0 :: aux_c5_O i).head? = some v :=
    Option.isSome_iff_exists.mp (List.isSome_head?.mpr hne)
  rw [aux_c5_junction _ _ _ _ u v hu hv]
  have key := aux_c5_S_junc n i hn hi hin u v hu hv
  have := congrArg (fun t : ℕ => (t : ℝ)) key
  push_cast at this
  linarith

theorem aux_c5_struct (n i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    circleSubtour n (i + 1) = (circleSubtour n i).insertIdx (1 + i / 2) ⟨i, hin⟩ := by
  apply List.map_injective_iff.mpr Fin.val_injective
  rw [List.map_insertIdx, aux_c5_mapS n (i + 1) (by omega) (by omega),
    aux_c5_mapS n i hi (by omega), aux_c5_S_step i hi, aux_c5_S_split i]
  have hl : (0 :: aux_c5_O i).length = 1 + i / 2 := by simp [aux_c5_O]; omega
  rw [← hl, aux_c5_insert_len]

end TSPHeuristics.KOpt

open TSPHeuristics.KOpt

theorem solution (n : ℕ) (hn : 6 ≤ n) :
    TSPHeuristics.Shared.IsInsertionRun (cycDist n) (circleSubtour n) (circleNode n (by omega)) ∧
      TSPHeuristics.Shared.IsNearestRule (cycDist n) (circleSubtour n) (circleNode n (by omega)) ∧
      TSPHeuristics.Shared.IsCheapestRule (cycDist n) (circleSubtour n) (circleNode n (by omega)) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply List.map_injective_iff.mpr Fin.val_injective
    rw [aux_c5_mapS n 1 le_rfl (by omega)]
    simp [aux_c5_S, aux_c5_O, aux_c5_E, circleNode]
  · intro i hi hin
    rw [aux_c5_node n _ i hin]
    refine ⟨?_, 1 + i / 2, ?_, aux_c5_struct n i hi hin, ?_⟩
    · rw [aux_c5_memT]; simp
    · rw [aux_c5_lenT n i hi (by omega)]; omega
    · intro pos' hpos'
      rw [aux_c5_EXF n i hn hi hin]
      exact aux_c5_LBF n i hn hi (by omega) ⟨i, hin⟩ le_rfl pos' hpos'
  · intro i hi hin x hx
    rw [aux_c5_node n _ i hin]
    unfold TSPHeuristics.Shared.distToTour
    have hmem : (⟨i - 1, by omega⟩ : Fin n) ∈ (circleSubtour n i).toFinset := by
      rw [List.mem_toFinset, aux_c5_memT]; simp; omega
    have hd1 : cycDist n ⟨i - 1, by omega⟩ ⟨i, hin⟩ = 1 := by
      show ((aux_c5_Dn n (i - 1) i : ℕ) : ℝ) = 1
      rw [aux_c5_Dn_eq n (i - 1) i (by omega) hin]
      norm_cast
      split_ifs <;> omega
    have h1 : (circleSubtour n i).toFinset.inf (fun y => ((cycDist n y ⟨i, hin⟩ : ℝ) : WithTop ℝ))
        ≤ ((1 : ℝ) : WithTop ℝ) := by
      rw [← hd1]
      exact Finset.inf_le (f := fun y => ((cycDist n y ⟨i, hin⟩ : ℝ) : WithTop ℝ)) hmem
    have h2 : ((1 : ℝ) : WithTop ℝ) ≤
        (circleSubtour n i).toFinset.inf (fun y => ((cycDist n y x : ℝ) : WithTop ℝ)) := by
      apply Finset.le_inf
      intro y hy
      rw [List.mem_toFinset, aux_c5_memT] at hy
      rw [aux_c5_memT] at hx
      have hxn := x.isLt
      apply WithTop.coe_le_coe.mpr
      show (1 : ℝ) ≤ ((aux_c5_Dn n y.val x.val : ℕ) : ℝ)
      rw [aux_c5_Dn_eq n y.val x.val y.isLt hxn]
      norm_cast
      split_ifs <;> omega
    exact h1.trans h2
  · intro i hi hin x hx
    rw [aux_c5_node n _ i hin]
    unfold TSPHeuristics.Shared.insCost
    rw [aux_c5_memT] at hx
    have hlen := aux_c5_lenT n i hi (by omega)
    apply sub_le_sub_right
    calc _ ≤ TSPHeuristics.Shared.cycleLength (cycDist n)
            ((circleSubtour n i).insertIdx (1 + i / 2) ⟨i, hin⟩) :=
          Finset.inf'_le (fun pos => TSPHeuristics.Shared.cycleLength (cycDist n)
            ((circleSubtour n i).insertIdx pos ⟨i, hin⟩)) (b := 1 + i / 2)
            (by rw [Finset.mem_range, hlen]; omega)
      _ = TSPHeuristics.Shared.cycleLength (cycDist n) (circleSubtour n i) + 2 := by
          rw [← aux_c5_struct n i hi hin, aux_c5_EXF n i hn hi hin]
      _ ≤ _ := by
          refine Finset.le_inf' _ _ (fun pos hpos => ?_)
          rw [Finset.mem_range] at hpos
          exact aux_c5_LBF n i hn hi (by omega) x (by omega) pos (by omega)
