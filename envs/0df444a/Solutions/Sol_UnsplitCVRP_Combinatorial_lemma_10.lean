-- Prove2me | solution 1 for UnsplitCVRP.Combinatorial.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T05:59:11.037792+00:00
-- url     : https://prove2.me/submissions/01b45ab7-7170-4d90-ae92-047bfa1f89c0

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

namespace CVRPAux
open SupplyChainTheory UnsplitCVRP.Combinatorial

theorem sum_filter_ne_nil {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c) :
    ∀ X : List (List (Fin (n + 1))),
      solutionCost c (X.filter (fun L => !L.isEmpty)) = solutionCost c X
  | [] => rfl
  | [] :: X => by
    have := sum_filter_ne_nil c hc X
    simp only [solutionCost] at this ⊢
    simp [this, routeCost_eq, pathLen, hc.refl]
  | (a :: l) :: X => by
    have := sum_filter_ne_nil c hc X
    simp only [solutionCost] at this ⊢
    simp [this]

end CVRPAux

open SupplyChainTheory UnsplitCVRP.Combinatorial CVRPAux in
theorem solution {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (R : List (List (Fin (n + 1))))
    (hR : IsSolution d R) :
    matchCost c d (bigIn d (1 / 3 : ℝ) (clients n)) ≤
      SupplyChainTheory.solutionCost c R := by
  set B := bigIn d (1 / 3 : ℝ) (clients n) with hBdef
  obtain ⟨hRL, hnd, hmem⟩ := hR
  set p : Fin (n + 1) → Bool := fun v => decide (v ∈ B) with hp
  set R' := (R.map (fun L => L.filter p)).filter (fun L => !L.isEmpty) with hR'
  have hfl : R'.flatten = R.flatten.filter p := by
    rw [hR', List.flatten_filter_not_isEmpty, List.filter_flatten]
  have hR'sol : IsSolutionOn d B R' := by
    refine ⟨?_, ?_, ?_⟩
    · intro L hL
      rw [hR', List.mem_filter, List.mem_map] at hL
      obtain ⟨⟨L0, hL0, rfl⟩, hne⟩ := hL
      obtain ⟨_, h0, hload⟩ := hRL L0 hL0
      refine ⟨by simpa using hne, fun h => h0 (List.mem_filter.mp h).1, ?_⟩
      refine le_trans ?_ hload
      unfold load
      apply List.Sublist.sum_le_sum (List.filter_sublist.map d)
      intro a ha
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
      exact (hd v (by rintro rfl; exact h0 hv)).1.le
    · rw [hfl]; exact hnd.filter _
    · intro v
      rw [hfl, List.mem_filter, hmem v]
      simp only [hp, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        simp only [hBdef, bigIn, Finset.mem_filter] at h
        exact h.1
  have hlen : ∀ L ∈ R', L.length ≤ 2 := by
    intro L hL
    have hLs := (hR'sol.1 L hL)
    have hbig : ∀ v ∈ L, 1 / 3 < d v := by
      intro v hv
      have : v ∈ R'.flatten := List.mem_flatten.mpr ⟨L, hL, hv⟩
      have := (hR'sol.2.2 v).1 this
      simp only [hBdef, bigIn, Finset.mem_filter] at this
      exact this.2
    have hlt := List.sum_lt_sum_of_ne_nil hLs.1 (fun _ => (1 / 3 : ℝ)) d hbig
    simp only [List.map_const', List.sum_replicate, nsmul_eq_mul] at hlt
    have h1 := hLs.2.2
    unfold load at h1
    by_contra hcon
    push_neg at hcon
    have : (3 : ℝ) ≤ L.length := by exact_mod_cast hcon
    linarith
  have hcost : solutionCost c R' ≤ solutionCost c R := by
    rw [hR', sum_filter_ne_nil c hc]
    unfold solutionCost
    rw [List.map_map]
    exact List.sum_le_sum (fun L _ => routeCost_sublist hc List.filter_sublist)
  refine le_trans ?_ hcost
  apply csInf_le
  · exact ⟨0, by rintro t ⟨A, _, _, rfl⟩; exact solutionCost_nonneg hc A⟩
  · exact ⟨R', hR'sol, hlen, rfl⟩
