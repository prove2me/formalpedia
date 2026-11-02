-- Prove2me | solution 1 for UnsplitCVRP.Combinatorial.tsp_le_opt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T05:59:10.468193+00:00
-- url     : https://prove2.me/submissions/c813f787-4c6c-4e29-972b-16f32fa966e4

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
    (hd : Demands d) (S : Finset (Fin (n + 1)))
    (hS : S ⊆ clients n) (R : List (List (Fin (n + 1))))
    (hR : IsSolution d R) :
    tspOn c S ≤ SupplyChainTheory.solutionCost c R := by
  obtain ⟨_, hnd, hmem⟩ := hR
  have hT : IsTourOn S (R.flatten.filter (fun v => decide (v ∈ S))) := by
    refine ⟨hnd.filter _, fun v => ?_⟩
    simp only [List.mem_filter, decide_eq_true_eq, hmem v]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  calc tspOn c S ≤ routeCost c (R.flatten.filter (fun v => decide (v ∈ S))) := by
        apply csInf_le
        · exact ⟨0, by rintro t ⟨A, _, rfl⟩; exact routeCost_nonneg hc A⟩
        · exact ⟨_, hT, rfl⟩
    _ ≤ routeCost c R.flatten := routeCost_sublist hc List.filter_sublist
    _ ≤ _ := flatten_walk hc R
