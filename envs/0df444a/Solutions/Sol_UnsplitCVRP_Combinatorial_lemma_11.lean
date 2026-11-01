-- Prove2me | solution 1 for UnsplitCVRP.Combinatorial.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T05:57:18.066474+00:00
-- url     : https://prove2.me/submissions/1b349555-c8c1-482a-94bb-40529ff19719

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting

namespace CVRPAux

open SupplyChainTheory UnsplitCVRP.Combinatorial

theorem finite_lists {α : Type} [Finite α] (m : ℕ) :
    {R : List (List α) | R.length ≤ m ∧ ∀ L ∈ R, L.length ≤ m}.Finite := by
  have hS' := List.finite_length_le α m
  have : Finite ↥{l : List α | l.length ≤ m} := hS'.to_subtype
  have hF := (List.finite_length_le (↥{l : List α | l.length ≤ m}) m).image
    (fun l => l.map Subtype.val)
  refine hF.subset ?_
  rintro R ⟨hRl, hR⟩
  lift R to List ↥{l : List α | l.length ≤ m} using hR
  exact ⟨R, by simpa using hRl, rfl⟩

theorem finite_sols {n : ℕ} :
    {R : List (List (Fin (n + 1))) | (∀ L ∈ R, L ≠ []) ∧ R.flatten.Nodup}.Finite := by
  refine (finite_lists (α := Fin (n + 1)) (n + 1)).subset ?_
  rintro R ⟨hne, hnd⟩
  have hlen : R.flatten.length ≤ n + 1 := by
    simpa using hnd.length_le_card
  refine ⟨?_, ?_⟩
  · have : R.length ≤ R.flatten.length := by
      rw [List.length_flatten]
      calc R.length = (R.map (fun _ => 1)).sum := by simp
        _ ≤ (R.map List.length).sum := by
          apply List.sum_le_sum
          intro L hL
          exact List.length_pos_iff.mpr (hne L hL)
    omega
  · intro L hL
    have : L.length ≤ R.flatten.length := by
      rw [List.length_flatten]
      exact List.le_sum_of_mem (List.mem_map_of_mem hL)
    omega

theorem sInf_attained {β : Type} (P : β → Prop) (f : β → ℝ)
    (hfin : {x | P x}.Finite) (hne : ∃ x, P x) :
    ∃ x, P x ∧ f x = sInf {t | ∃ x, P x ∧ t = f x} := by
  have hT : {t | ∃ x, P x ∧ t = f x} = f '' {x | P x} := by
    ext t; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  obtain ⟨x0, hx0⟩ := hne
  have hmem := Set.Nonempty.csInf_mem (s := f '' {x | P x}) ⟨f x0, x0, hx0, rfl⟩
    (hfin.image f)
  rw [hT]
  obtain ⟨x, hx, hfx⟩ := hmem
  exact ⟨x, hx, hfx⟩

theorem sInf_le_of {β : Type} (P : β → Prop) (f : β → ℝ)
    (hfin : {x | P x}.Finite) (x : β) (hx : P x) :
    sInf {t | ∃ x, P x ∧ t = f x} ≤ f x := by
  have hT : {t | ∃ x, P x ∧ t = f x} = f '' {x | P x} := by
    ext t; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [hT]
  exact csInf_le (hfin.image f).bddBelow ⟨x, hx, rfl⟩

/-- Length of an open walk. -/
def pathLen {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) : List (Fin (n + 1)) → ℝ
  | x :: y :: t => c x y + pathLen c (y :: t)
  | _ => 0

theorem zip_sum_eq {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (b : Fin (n + 1)) :
    ∀ (l : List (Fin (n + 1))) (a : Fin (n + 1)),
      (List.zipWith c (a :: l) (l ++ [b])).sum = pathLen c (a :: l ++ [b])
  | [], a => by simp [pathLen]
  | h :: t, a => by
    have := zip_sum_eq c b t h
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons] at this ⊢
    rw [this]; rfl

theorem routeCost_eq {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (L : List (Fin (n + 1))) :
    routeCost c L = pathLen c (0 :: L ++ [0]) := by
  unfold routeCost closedLength
  rw [← zip_sum_eq]
  congr 2
  simp [List.rotate_cons_succ]

theorem pathLen_append {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (m : Fin (n + 1))
    (l' : List (Fin (n + 1))) :
    ∀ l : List (Fin (n + 1)), pathLen c (l ++ m :: l') = pathLen c (l ++ [m]) + pathLen c (m :: l')
  | [] => by simp [pathLen]
  | [x] => by simp [pathLen]
  | x :: y :: t => by
    have := pathLen_append c m l' (y :: t)
    simp only [List.cons_append] at this ⊢
    simp only [pathLen]
    rw [this]; ring

theorem pathLen_nonneg {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c) :
    ∀ l : List (Fin (n + 1)), 0 ≤ pathLen c l
  | [] => by simp [pathLen]
  | [x] => by simp [pathLen]
  | x :: y :: t => by
    simp only [pathLen]
    have := pathLen_nonneg hc (y :: t)
    linarith [hc.nonneg x y]

theorem routeCost_nonneg {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (L : List (Fin (n + 1))) : 0 ≤ routeCost c L := by
  rw [routeCost_eq]; exact pathLen_nonneg hc _

theorem solutionCost_nonneg {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (R : List (List (Fin (n + 1)))) : 0 ≤ solutionCost c R := by
  unfold solutionCost
  apply List.sum_nonneg
  intro x hx
  obtain ⟨L, _, rfl⟩ := List.mem_map.mp hx
  exact routeCost_nonneg hc L

theorem pathLen_drop1 {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (a x : Fin (n + 1)) (m : List (Fin (n + 1))) (hm : m ≠ []) :
    pathLen c (a :: m) ≤ pathLen c (a :: x :: m) := by
  obtain ⟨y, m', rfl⟩ := List.exists_cons_of_ne_nil hm
  simp only [pathLen]
  linarith [hc.triangle a y x]

/-- Shortcutting: deleting interior points does not increase walk length. -/
theorem pathLen_sublist {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    (b : Fin (n + 1)) {l₁ l₂ : List (Fin (n + 1))} (h : l₁.Sublist l₂) :
    ∀ a : Fin (n + 1), pathLen c (a :: l₁ ++ [b]) ≤ pathLen c (a :: l₂ ++ [b]) := by
  induction h with
  | slnil => intro a; exact le_refl _
  | cons x h ih =>
    intro a
    refine (ih a).trans ?_
    simp only [List.cons_append]
    exact pathLen_drop1 hc a x _ (by simp)
  | cons_cons x h ih =>
    intro a
    simp only [List.cons_append, pathLen]
    have := ih x
    simp only [List.cons_append] at this
    linarith

theorem routeCost_sublist {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    {l₁ l₂ : List (Fin (n + 1))} (h : l₁.Sublist l₂) : routeCost c l₁ ≤ routeCost c l₂ := by
  rw [routeCost_eq, routeCost_eq]; exact pathLen_sublist hc 0 h 0

theorem two_c_le_routeCost {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c)
    {L : List (Fin (n + 1))} {v : Fin (n + 1)} (hv : v ∈ L) : 2 * c 0 v ≤ routeCost c L := by
  have := routeCost_sublist hc (List.singleton_sublist.mpr hv)
  rw [routeCost_eq] at this
  simp [pathLen] at this
  linarith [hc.symm v 0]

theorem flatten_walk {n : ℕ} {c : Fin (n + 1) → Fin (n + 1) → ℝ} (hc : VRPMetric c) :
    ∀ R : List (List (Fin (n + 1))), routeCost c R.flatten ≤ solutionCost c R
  | [] => by simp [routeCost_eq, pathLen, solutionCost, hc.refl]
  | L :: R => by
    have ih := flatten_walk hc R
    have h1 : routeCost c (L ++ R.flatten) ≤ pathLen c (0 :: L ++ [0] ++ R.flatten ++ [0]) := by
      rw [routeCost_eq]
      have := pathLen_sublist hc 0 (l₁ := L ++ R.flatten) (l₂ := L ++ [0] ++ R.flatten)
        (by simp) 0
      simpa using this
    have h2 : pathLen c (0 :: L ++ [0] ++ R.flatten ++ [0]) =
        routeCost c L + routeCost c R.flatten := by
      rw [routeCost_eq, routeCost_eq]
      have := pathLen_append c 0 (R.flatten ++ [0]) (0 :: L)
      simpa using this
    simp only [List.flatten_cons, solutionCost, List.map_cons, List.sum_cons] at h1 h2 ih ⊢
    linarith

end CVRPAux

open SupplyChainTheory UnsplitCVRP.Combinatorial CVRPAux in
theorem solution {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) :
    matchCost c d (bigIn d (1 / 3 : ℝ) (clients n)) ≤
      radialCount c (bigIn d (1 / 3 : ℝ) (clients n)) := by
  set B := bigIn d (1 / 3 : ℝ) (clients n) with hBdef
  have hB : ∀ v ∈ B, v ≠ 0 := by
    intro v hv; simp only [hBdef, bigIn, clients, Finset.mem_filter, Finset.mem_erase] at hv
    exact hv.1.1
  have hfl : (B.toList.map (fun a => [a])).flatten = B.toList := by
    generalize B.toList = A
    induction A with
    | nil => rfl
    | cons a t ih => simp [ih]
  have hcost : solutionCost c (B.toList.map (fun a => [a])) = radialCount c B := by
    unfold solutionCost radialCount
    rw [List.map_map, ← Finset.sum_map_toList B (fun v => 2 * c 0 v)]
    congr 1
    apply List.map_congr_left
    intro v _
    simp [routeCost_eq, pathLen, hc.refl, hc.symm v 0]
    ring
  unfold matchCost
  rw [← hcost]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨R, _, _, rfl⟩
    exact solutionCost_nonneg hc R
  · refine ⟨_, ⟨?_, ?_, ?_⟩, ?_, rfl⟩
    · intro L hL
      simp only [List.mem_map] at hL
      obtain ⟨a, ha, rfl⟩ := hL
      have ha' : a ∈ B := Finset.mem_toList.mp ha
      refine ⟨by simp, ?_, by simpa [load] using (hd a (hB a ha')).2⟩
      simp only [List.mem_singleton]
      rintro rfl; exact hB 0 ha' rfl
    · rw [hfl]; exact B.nodup_toList
    · intro v; rw [hfl]; simp
    · intro L hL
      simp only [List.mem_map] at hL
      obtain ⟨a, ha, rfl⟩ := hL
      simp
