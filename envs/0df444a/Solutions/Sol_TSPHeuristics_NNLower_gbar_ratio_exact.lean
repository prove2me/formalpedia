-- Prove2me | solution 1 for TSPHeuristics.NNLower.gbar_ratio_exact
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T20:30:19.738984+00:00
-- url     : https://prove2.me/submissions/d05472dd-6350-48ff-be46-e680cae7144c

import Definitions.Def_TSPHeuristics_NNLower_TSPModel
import Definitions.Def_TSPHeuristics_NNLower_ShortestPathMetric
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily
import Theorems.Thm_TSPHeuristics_NNLower_gbar_edge_lengths
import Theorems.Thm_TSPHeuristics_NNLower_optimal_gbar
import Mathlib

namespace TSPAux
open TSPHeuristics.NNLower

/-! ### Walks -/

theorem walk_single {E : List (ℕ × ℕ × ℝ)} {x y : ℕ} {w : ℝ}
    (he : (x, y, w) ∈ E ∨ (y, x, w) ∈ E) : WalkCost E x y w := by
  simpa using WalkCost.cons he (WalkCost.nil y)

theorem walk_trans {E : List (ℕ × ℕ × ℝ)} {x y z : ℕ} {c₁ c₂ : ℝ}
    (h₁ : WalkCost E x y c₁) (h₂ : WalkCost E y z c₂) : WalkCost E x z (c₁ + c₂) := by
  induction h₁ with
  | nil x => simpa using h₂
  | cons he h ih =>
    have := WalkCost.cons he (ih h₂)
    simpa [add_assoc] using this

theorem walk_symm {E : List (ℕ × ℕ × ℝ)} {x y : ℕ} {c : ℝ} (h : WalkCost E x y c) :
    WalkCost E y x c := by
  induction h with
  | nil x => exact WalkCost.nil x
  | cons he h ih =>
    have := walk_trans ih (walk_single he.symm)
    simpa [add_comm] using this

theorem spDist_symm (E : List (ℕ × ℕ × ℝ)) (x y : ℕ) : spDist E x y = spDist E y x := by
  unfold spDist
  congr 1
  ext c
  exact ⟨walk_symm, walk_symm⟩

/-! ### Sums along a node list -/

/-- The sum of `d` over consecutive pairs of a list. -/
def pathSum (d : ℕ → ℕ → ℝ) : List ℕ → ℝ
  | a :: b :: t => d a b + pathSum d (b :: t)
  | _ => 0

theorem pathSum_append (d : ℕ → ℕ → ℝ) (ys : List ℕ) (x b : ℕ) (l₂ : List ℕ) :
    pathSum d (ys ++ x :: b :: l₂) = pathSum d (ys ++ [x]) + d x b + pathSum d (b :: l₂) := by
  induction ys with
  | nil => simp [pathSum]
  | cons a ys ih =>
    cases ys with
    | nil => simp [pathSum]; ring
    | cons a' ys' =>
      have := ih
      simp only [List.cons_append, pathSum] at this ⊢
      rw [this]
      ring

theorem pathSum_map (d : ℕ → ℕ → ℝ) (f : ℕ → ℕ) (l : List ℕ) :
    pathSum d (l.map f) = pathSum (fun a b => d (f a) (f b)) l := by
  induction l with
  | nil => simp [pathSum]
  | cons a t ih =>
    cases t with
    | nil => simp [pathSum]
    | cons b t =>
      simp only [List.map_cons, pathSum] at ih ⊢
      rw [ih]

theorem pathSum_eq_sum (d : ℕ → ℕ → ℝ) : ∀ (m : ℕ) (l : List ℕ), l.length = m + 1 →
    pathSum d l = ∑ k ∈ Finset.range m, d (l.getD k 0) (l.getD (k + 1) 0) := by
  intro m
  induction m with
  | zero =>
    intro l hl
    match l, hl with
    | [a], _ => simp [pathSum]
  | succ m ih =>
    intro l hl
    match l, hl with
    | a :: b :: t, hl =>
      have h1 : (b :: t).length = m + 1 := by simpa using hl
      rw [pathSum, ih (b :: t) h1, Finset.sum_range_succ' _ m]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

theorem tour_sum (d : ℕ → ℕ → ℝ) {n : ℕ} (hn : 0 < n) (l : List ℕ) (hl : l.length = n)
    (τ : Equiv.Perm (Fin n)) (hτ : ∀ k : Fin n, (τ k : ℕ) = l.getD k 0) :
    ∑ k, d (τ k) (τ (finRotate n k)) = pathSum d l + d (l.getD (n - 1) 0) (l.getD 0 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_castSucc, pathSum_eq_sum d m l hl]
  have h1 : ∀ i : Fin m, finRotate (m + 1) (Fin.castSucc i) = i.succ := by
    intro i
    simp
  have h2 : ∑ i : Fin m, d (τ (Fin.castSucc i)) (τ (finRotate (m + 1) (Fin.castSucc i)))
      = ∑ k ∈ Finset.range m, d (l.getD k 0) (l.getD (k + 1) 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => d (l.getD k 0) (l.getD (k + 1) 0)) m]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i, hτ, hτ]
    simp
  rw [h2, finRotate_last, hτ, hτ]
  simp

/-! ### The path `P_i` -/

theorem pathP_length : ∀ i, 1 ≤ i → (pathP i).length = numNodes i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => simp [pathP, numNodes]
  | succ j hj ih =>
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [pathP, List.length_append, List.length_map, ih, List.length_cons, List.length_nil]
    simp only [numNodes] at *
    have : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    have h2 : 2 ^ (k + 1 + 1 + 1) = 2 * 2 ^ (k + 1 + 1) := by ring
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    omega

theorem pathP_head : ∀ i, 1 ≤ i → (pathP i).head? = some 0 := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => simp [pathP]
  | succ j hj ih =>
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [pathP]
    rw [List.append_assoc, List.head?_append, ih]
    simp

theorem pathP_last : ∀ i, 1 ≤ i → (pathP i).getLast? = some (middle i) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => simp [pathP, middle]
  | succ j hj ih =>
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp [pathP, middle, numNodes]

theorem pathSum_pathP : ∀ (j : ℕ) (d : ℕ → ℕ → ℝ),
    (∀ e ∈ edgesF (j + 1), d e.1 e.2.1 = e.2.2 ∧ d e.2.1 e.1 = e.2.2) →
    pathSum d (pathP (j + 1)) = pathLength (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro d hd
    have h1 := hd (0, 2, 1) (by simp [edgesF])
    have h2 := hd (1, 2, 1) (by simp [edgesF])
    simp [pathP, pathLength, pathSum, h1.1, h2.2]
    norm_num
  | succ j ih =>
    intro d hd
    set s := numNodes (j + 1) with hs
    have hL : ∀ e ∈ edgesF (j + 1), d e.1 e.2.1 = e.2.2 ∧ d e.2.1 e.1 = e.2.2 := by
      intro e he
      exact hd e (by
        simp only [edgesF]
        exact List.mem_append_left _ (List.mem_append_left _ he))
    have hR : ∀ e ∈ edgesF (j + 1),
        (fun a b => d (a + (s + 1)) (b + (s + 1))) e.1 e.2.1 = e.2.2 ∧
        (fun a b => d (a + (s + 1)) (b + (s + 1))) e.2.1 e.1 = e.2.2 := by
      intro e he
      exact hd (e.1 + (s + 1), e.2.1 + (s + 1), e.2.2) (by
        simp only [edgesF]
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨e, he, rfl⟩)))
    have hBE := hd (middle (j + 1), s + 1, ell (j + 1)) (by simp [edgesF, hs])
    have hDF := hd (s, s + 1 + middle (j + 1), ell (j + 1)) (by simp [edgesF, hs])
    have hP := ih d hL
    have hQ := ih (fun a b => d (a + (s + 1)) (b + (s + 1))) hR
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp (pathP_last (j + 1) (by omega))
    obtain ⟨t, ht⟩ : ∃ t, pathP (j + 1) = 0 :: t := by
      have := pathP_head (j + 1) (by omega)
      cases h : pathP (j + 1) with
      | nil => simp [h] at this
      | cons a t => simp [h] at this; exact ⟨t, by simp [this]⟩
    set m := middle (j + 1) with hm
    have hQ1 : (pathP (j + 1)).map (fun a => a + (s + 1)) = ys.map (fun a => a + (s + 1)) ++ [m + (s + 1)] := by
      rw [hys]; simp
    have hQ0 : (pathP (j + 1)).map (fun a => a + (s + 1)) = (s + 1) :: t.map (fun a => a + (s + 1)) := by
      rw [ht]; simp
    have hsumQ : pathSum d ((pathP (j + 1)).map (fun a => a + (s + 1))) = pathLength (j + 1) := by
      rw [pathSum_map]; exact hQ
    have e : pathP (j + 1 + 1) = ys ++ m :: (s + 1) :: (t.map (fun a => a + (s + 1)) ++ [s]) := by
      show pathP (j + 1) ++ (pathP (j + 1)).map (fun a => a + (s + 1)) ++ [s] = _
      rw [List.append_assoc, hQ0, hys]
      simp
    have e2 : (s + 1) :: (t.map (fun a => a + (s + 1)) ++ [s])
        = ys.map (fun a => a + (s + 1)) ++ (m + (s + 1)) :: s :: [] := by
      have h3 := hQ0.symm.trans hQ1
      calc (s + 1) :: (t.map (fun a => a + (s + 1)) ++ [s])
          = ((s + 1) :: t.map (fun a => a + (s + 1))) ++ [s] := by simp
        _ = _ := by rw [h3]; simp
    have hP' : pathSum d (ys ++ [m]) = pathLength (j + 1) := by rw [← hys]; exact hP
    have hQ' : pathSum d (ys.map (fun a => a + (s + 1)) ++ [m + (s + 1)]) = pathLength (j + 1) := by
      rw [← hQ1]; exact hsumQ
    have h1 : d m (s + 1) = ell (j + 1) := hBE.1
    have h2 : d (m + (s + 1)) s = ell (j + 1) := by rw [add_comm]; exact hDF.2
    rw [e, pathSum_append, hP', e2, pathSum_append, hQ', h1, h2]
    simp only [pathSum, pathLength]
    ring

end TSPAux

open TSPHeuristics.NNLower TSPAux in
theorem solution (i : ℕ) (hi : 1 ≤ i) (τ : Equiv.Perm (Fin (numNodes i)))
    (hτ : ∀ k : Fin (numNodes i), (τ k : ℕ) = (pathP i).getD k 0) :
    tourLength (gbar i) τ = pathLength i + ell i - 1 ∧
      tourLength (gbar i) τ / optimal (gbar i) =
        (pathLength i + ell i - 1) / ((2 : ℝ) ^ (i + 1) - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  set d : ℕ → ℕ → ℝ := fun a b => spDist (edgesG (j + 1)) a b with hd_def
  have hedge : ∀ e ∈ edgesG (j + 1), d e.1 e.2.1 = e.2.2 ∧ d e.2.1 e.1 = e.2.2 := by
    intro e he
    have h := gbar_edge_lengths (j + 1) hi e he
    refine ⟨h, ?_⟩
    show spDist (edgesG (j + 1)) e.2.1 e.1 = e.2.2
    rw [spDist_symm]; exact h
  have hdF : ∀ e ∈ edgesF (j + 1), d e.1 e.2.1 = e.2.2 ∧ d e.2.1 e.1 = e.2.2 :=
    fun e he => hedge e (by simp [edgesG, he])
  have hn : 0 < numNodes (j + 1) := by simp [numNodes]
  have hsum : tourLength (gbar (j + 1)) τ
      = pathSum d (pathP (j + 1))
        + d ((pathP (j + 1)).getD (numNodes (j + 1) - 1) 0) ((pathP (j + 1)).getD 0 0) :=
    tour_sum d hn (pathP (j + 1)) (pathP_length (j + 1) hi) τ hτ
  have hlast : (pathP (j + 1)).getD (numNodes (j + 1) - 1) 0 = middle (j + 1) := by
    have h := pathP_last (j + 1) hi
    rw [List.getLast?_eq_getElem?, pathP_length (j + 1) hi] at h
    simp [List.getD_eq_getElem?_getD, h]
  have hfirst : (pathP (j + 1)).getD 0 0 = 0 := by
    have h := pathP_head (j + 1) hi
    rw [List.head?_eq_getElem?] at h
    simp [List.getD_eq_getElem?_getD, h]
  have hret : d (middle (j + 1)) 0 = ell (j + 1) - 1 :=
    (hedge (middle (j + 1), 0, ell (j + 1) - 1) (by simp [edgesG])).1
  have hlen : tourLength (gbar (j + 1)) τ = pathLength (j + 1) + ell (j + 1) - 1 := by
    rw [hsum, hlast, hfirst, hret, pathSum_pathP j d hdF]
    ring
  refine ⟨hlen, ?_⟩
  rw [hlen, optimal_gbar (j + 1) hi]
