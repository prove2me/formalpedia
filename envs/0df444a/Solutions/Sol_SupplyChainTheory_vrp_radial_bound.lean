-- Prove2me | solution 1 for SupplyChainTheory.vrp_radial_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T21:54:19.49606+00:00
-- url     : https://prove2.me/submissions/ca08f619-dc61-4927-8bd4-8e05b29c6b58

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp

open SupplyChainTheory

/-! ### Closed walks given as lists -/

/-- The last element of `h :: t`. -/
private def lastD {α : Type*} : α → List α → α
  | h, [] => h
  | _, b :: t => lastD b t

/-- The length of the open path through a list. -/
private def pathLen {α : Type*} (c : α → α → ℝ) : List α → ℝ
  | a :: b :: l => c a b + pathLen c (b :: l)
  | _ => 0

private lemma zipWith_append_sum {α : Type*} (c : α → α → ℝ) (e : α) :
    ∀ (h : α) (t : List α),
      (List.zipWith c (h :: t) (t ++ [e])).sum = pathLen c (h :: t) + c (lastD h t) e
  | h, [] => by simp [pathLen, lastD]
  | h, b :: t => by
    rw [List.cons_append, List.zipWith_cons_cons, List.sum_cons, zipWith_append_sum c e b t]
    simp only [pathLen, lastD]; ring

/-- A closed walk is its open path plus the closing edge. -/
private lemma closedLength_cons {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (h : Fin (n + 1))
    (t : List (Fin (n + 1))) : closedLength c (h :: t) = pathLen c (h :: t) + c (lastD h t) h := by
  rw [closedLength, List.rotate_cons_succ, List.rotate_zero, zipWith_append_sum]

private lemma pathLen_nonneg {α : Type*} (c : α → α → ℝ) (hc : ∀ i j, 0 ≤ c i j) :
    ∀ l : List α, 0 ≤ pathLen c l
  | [] => le_refl _
  | [_] => le_refl _
  | a :: b :: l => by
    simp only [pathLen]; linarith [hc a b, pathLen_nonneg c hc (b :: l)]

private lemma routeCost_nonneg {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (L : List (Fin (n + 1))) : 0 ≤ routeCost c L := by
  rw [routeCost, closedLength_cons]
  linarith [pathLen_nonneg c hc.nonneg (0 :: L), hc.nonneg (lastD 0 L) 0]

/-- Along a path from `h`, any visited node `v` splits it: `c(h,v) + c(v,end) ≤ path`. -/
private lemma split_le {α : Type*} (c : α → α → ℝ) (hrefl : ∀ i, c i i = 0)
    (htri : ∀ i j k, c i j ≤ c i k + c k j) :
    ∀ (h : α) (t : List α), ∀ v ∈ h :: t, c h v + c v (lastD h t) ≤ pathLen c (h :: t)
  | h, [], v, hv => by
    rw [List.mem_singleton] at hv; subst hv; simp [pathLen, lastD, hrefl]
  | h, b :: t, v, hv => by
    have ih := split_le c hrefl htri b t
    simp only [pathLen, lastD]
    rcases List.mem_cons.mp hv with rfl | hv'
    · have := ih b List.mem_cons_self
      rw [hrefl] at this ⊢
      linarith [htri v (lastD b t) b]
    · have := ih v hv'
      linarith [htri h v b]

/-- A route visits every one of its customers and returns: `2 c(0,v) ≤ routeCost`. -/
private lemma two_depot_le_routeCost {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (L : List (Fin (n + 1))) (v : Fin (n + 1)) (hv : v ∈ L) : 2 * c 0 v ≤ routeCost c L := by
  rw [routeCost, closedLength_cons]
  have := split_le c hc.refl hc.triangle 0 L v (List.mem_cons_of_mem _ hv)
  have h2 := hc.triangle v 0 (lastD 0 L)
  rw [hc.symm v 0] at h2
  linarith

/-- Concatenating two routes and skipping the depot in between is no longer. -/
private lemma routeCost_append_le {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (A B : List (Fin (n + 1))) : routeCost c (A ++ B) ≤ routeCost c A + routeCost c B := by
  rcases B with _ | ⟨b, B⟩
  · simp only [List.append_nil]; linarith [routeCost_nonneg c hc []]
  have hpath : ∀ (h : Fin (n + 1)) (t : List (Fin (n + 1))),
      pathLen c (h :: (t ++ b :: B)) = pathLen c (h :: t) + c (lastD h t) b + pathLen c (b :: B) := by
    intro h t
    induction t generalizing h with
    | nil => simp [pathLen, lastD]
    | cons a t ih => simp only [List.cons_append, pathLen, lastD]; rw [ih]; ring
  have hlast : ∀ (h : Fin (n + 1)) (t : List (Fin (n + 1))), lastD h (t ++ b :: B) = lastD b B := by
    intro h t
    induction t generalizing h with
    | nil => rfl
    | cons a t ih => exact ih a
  simp only [routeCost, closedLength_cons]
  rw [hpath 0 A, hlast]
  simp only [pathLen, lastD]
  have := hc.triangle (lastD 0 A) b 0
  linarith

/-- The routes of a solution, concatenated. -/
private lemma routeCost_flatten_le {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c) :
    ∀ R : List (List (Fin (n + 1))), routeCost c (R.flatMap id) ≤ solutionCost c R
  | [] => by simp [solutionCost, routeCost, closedLength, hc.refl]
  | L :: R => by
    rw [List.flatMap_cons, solutionCost, List.map_cons, List.sum_cons]
    have := routeCost_flatten_le c hc R
    rw [solutionCost] at this
    have h2 := routeCost_append_le c hc L (R.flatMap id)
    simp only [id] at h2 ⊢
    linarith

/-- The list of all customers. -/
private def customers (n : ℕ) : List (Fin (n + 1)) := (List.finRange n).map Fin.succ

private lemma customers_isTour (n : ℕ) : IsCustomerTour (customers n) := by
  refine ⟨(List.nodup_finRange n).map (Fin.succ_injective _), ?_, fun v hv => ?_⟩
  · simp [customers, Fin.succ_ne_zero]
  · obtain ⟨w, rfl⟩ := Fin.exists_succ_eq.mpr hv
    simp [customers]

/-- Singleton routes form a feasible solution when `C ≥ 1`. -/
private lemma exists_solution {n : ℕ} (C : ℕ) (hC : 1 ≤ C) :
    ∃ R : List (List (Fin (n + 1))), IsVRPSolution C R := by
  refine ⟨(customers n).map (fun v => [v]), ?_, ?_, ?_⟩
  · intro L hL
    simp only [List.mem_map] at hL
    obtain ⟨v, hv, rfl⟩ := hL
    refine ⟨by simp, by simpa using hC, ?_⟩
    simp only [List.mem_singleton]
    intro h; rw [← h] at hv; exact (customers_isTour n).2.1 hv
  · have : ((customers n).map (fun v => [v])).flatMap id = customers n := by
      simp [List.flatMap_map]
    rw [this]; exact (customers_isTour n).1
  · intro v hv
    have : ((customers n).map (fun v => [v])).flatMap id = customers n := by
      simp [List.flatMap_map]
    rw [this]; exact (customers_isTour n).2.2 v hv

private lemma vrp_set_nonempty {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (C : ℕ) (hC : 1 ≤ C) :
    {z | ∃ R, IsVRPSolution C R ∧ z = solutionCost c R}.Nonempty := by
  obtain ⟨R, hR⟩ := exists_solution (n := n) C hC
  exact ⟨_, R, hR, rfl⟩

private lemma solutionCost_nonneg {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (R : List (List (Fin (n + 1)))) : 0 ≤ solutionCost c R :=
  List.sum_nonneg (fun x hx => by
    simp only [List.mem_map] at hx; obtain ⟨L, _, rfl⟩ := hx; exact routeCost_nonneg c hc L)

private lemma vrp_bddBelow {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c) (C : ℕ) :
    BddBelow {z | ∃ R, IsVRPSolution C R ∧ z = solutionCost c R} :=
  ⟨0, by rintro z ⟨R, _, rfl⟩; exact solutionCost_nonneg c hc R⟩

/-- Summing a per-customer quantity over all routes of a solution sums it over all customers. -/
private lemma sum_over_solution {n : ℕ} (f : Fin (n + 1) → ℝ) (hf0 : f 0 = 0) (C : ℕ)
    (R : List (List (Fin (n + 1)))) (hR : IsVRPSolution C R) :
    (R.map (fun L => (L.map f).sum)).sum = ∑ i, f i := by
  have hflat : (R.map (fun L => (L.map f).sum)).sum = ((R.flatMap id).map f).sum := by
    clear hR
    induction R with
    | nil => simp
    | cons L R ih => simp [List.flatMap_cons, ih]
  rw [hflat, ← List.sum_toFinset f hR.2.1]
  have hset : (R.flatMap id).toFinset = Finset.univ.erase 0 := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hv h0
      subst h0
      obtain ⟨L, hL, h0L⟩ := List.mem_flatMap.mp hv
      exact (hR.1 L hL).2.2 h0L
    · exact hR.2.2 v
  rw [hset, Finset.sum_erase _ hf0]

theorem solution {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (hn : 1 ≤ n) (C : ℕ) (hC : 1 ≤ C) :
    2 * ((n : ℝ) / C) * avgDepotDist c ≤ vrpOpt c C := by
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hleft : 2 * ((n : ℝ) / C) * avgDepotDist c = 2 * (∑ i, c 0 i) / C := by
    rw [avgDepotDist]; field_simp
  rw [hleft]
  refine le_csInf (vrp_set_nonempty c C hC) ?_
  rintro z ⟨R, hR, rfl⟩
  -- Each route is at least twice its farthest customer, hence `2/C` times its depot distances.
  have hroute : ∀ L ∈ R, (L.map (c 0)).sum ≤ (C : ℝ) / 2 * routeCost c L := by
    intro L hL
    have h1 : (L.map (c 0)).sum ≤ (L.map (c 0)).length • (routeCost c L / 2) := by
      refine List.sum_le_card_nsmul _ _ (fun x hx => ?_)
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      linarith [two_depot_le_routeCost c hc L v hv]
    rw [List.length_map, nsmul_eq_mul] at h1
    have hlen : (L.length : ℝ) ≤ C := by exact_mod_cast (hR.1 L hL).2.1
    have hnn := routeCost_nonneg c hc L
    nlinarith
  have hsum := List.sum_le_sum (l := R) hroute
  rw [sum_over_solution (c 0) (hc.refl 0) C R hR, List.sum_map_mul_left] at hsum
  rw [div_le_iff₀ hCpos, solutionCost]
  linarith
