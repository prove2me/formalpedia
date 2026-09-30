-- Prove2me | solution 1 for SupplyChainTheory.iotp_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T21:59:37.595002+00:00
-- url     : https://prove2.me/submissions/bb3df3f4-7955-44b5-89a5-c4a85d02fb80

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
/-- A periodic sum over any window of one period is the sum over `[0, N)`. -/
private lemma sum_Ico_period (f : ℕ → ℝ) (N : ℕ) (hf : ∀ i, f (i + N) = f i) :
    ∀ a, ∑ i ∈ Finset.Ico a (a + N), f i = ∑ i ∈ Finset.range N, f i := by
  intro a
  induction a with
  | zero => rw [Nat.zero_add, Finset.range_eq_Ico]
  | succ a ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Nat.add_zero, Finset.Ico_self, Finset.sum_empty, Finset.range_zero]
    rw [← ih, Finset.sum_eq_sum_Ico_succ_bot (by omega : a < a + N),
      show a + 1 + N = a + N + 1 by omega, Finset.sum_Ico_succ_top (by omega : a + 1 ≤ a + N), hf]
    ring

private lemma mono_chain (q : ℕ → ℕ) (K : ℕ) (hq : ∀ j < K, q j ≤ q (j + 1)) : q 0 ≤ q K := by
  induction K with
  | zero => exact le_refl _
  | succ K ih => exact (ih (fun j hj => hq j (by omega))).trans (hq K (by omega))

/-- Telescoping a sum over consecutive windows `[q j, q (j+1))`. -/
private lemma sum_windows (f : ℕ → ℝ) (q : ℕ → ℕ) (K : ℕ) (hq : ∀ j < K, q j ≤ q (j + 1)) :
    ∑ j ∈ Finset.range K, ∑ i ∈ Finset.Ico (q j) (q (j + 1)), f i
      = ∑ i ∈ Finset.Ico (q 0) (q K), f i := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih (fun j hj => hq j (by omega)),
      Finset.sum_Ico_consecutive _ (mono_chain q K (fun j hj => hq j (by omega))) (hq K (by omega))]

/-! ### Routes along consecutive positions of a tour -/

private lemma pathLen_block {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (x : ℕ → Fin (n + 1)) :
    ∀ (m a : ℕ), pathLen c ((List.range' a (m + 1)).map x)
        = ∑ i ∈ Finset.Ico a (a + m), c (x i) (x (i + 1))
      ∧ lastD (x a) ((List.range' (a + 1) m).map x) = x (a + m)
  | 0, a => by simp [pathLen, lastD]
  | m + 1, a => by
    obtain ⟨ih1, ih2⟩ := pathLen_block c x m (a + 1)
    have e1 : (List.range' a (m + 1 + 1)).map x = x a :: (List.range' (a + 1) (m + 1)).map x := by
      simp [List.range'_succ]
    have e2 : (List.range' (a + 1) (m + 1)).map x = x (a + 1) :: (List.range' (a + 1 + 1) m).map x := by
      simp [List.range'_succ]
    refine ⟨?_, ?_⟩
    · rw [e1, e2]
      show c (x a) (x (a + 1)) + pathLen c (x (a + 1) :: (List.range' (a + 1 + 1) m).map x) = _
      rw [← e2, ih1, Finset.sum_eq_sum_Ico_succ_bot (by omega : a < a + (m + 1)),
        show a + (m + 1) = a + 1 + m from by omega]
    · rw [e2]
      show lastD (x (a + 1)) ((List.range' (a + 1 + 1) m).map x) = _
      rw [ih2]; congr 1; omega

/-- The cost of the route through positions `a, a+1, …, a+m`. -/
private lemma routeCost_block {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (x : ℕ → Fin (n + 1))
    (m a : ℕ) : routeCost c ((List.range' a (m + 1)).map x)
      = c 0 (x a) + ∑ i ∈ Finset.Ico a (a + m), c (x i) (x (i + 1)) + c (x (a + m)) 0 := by
  obtain ⟨h1, h2⟩ := pathLen_block c x m a
  rw [routeCost, closedLength_cons]
  rw [List.range'_succ, List.map_cons] at h1 ⊢
  simp only [pathLen, lastD]
  rw [h1, h2]

/-- Summing a periodic function over any shift of one period. -/
private lemma sum_range_shift (f : ℕ → ℝ) (N : ℕ) (hf : ∀ i, f (i + N) = f i) (a : ℕ) :
    ∑ j ∈ Finset.range N, f (j + a) = ∑ j ∈ Finset.range N, f j := by
  rw [← sum_Ico_period f N hf a, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  exact Finset.sum_congr rfl (fun j _ => by rw [add_comm])

theorem solution {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : VRPMetric c)
    (hn : 1 ≤ n) (C : ℕ) (hC : 1 ≤ C) (L : List (Fin (n + 1))) (hL : IsCustomerTour L) :
    ∃ R, IsVRPSolution C R ∧ solutionCost c R
      ≤ 2 * ⌈(n : ℝ) / C⌉₊ * avgDepotDist c + (1 - (⌈(n : ℝ) / C⌉₊ : ℝ) / n) * routeCost c L := by
  obtain ⟨hnd, h0L, hall⟩ := hL
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- `ℓ = ⌈n/C⌉` routes: `n ≤ ℓ C` and `(ℓ - 1) C < n`.
  set ℓ := ⌈(n : ℝ) / C⌉₊ with hℓ
  have hℓC : n ≤ ℓ * C := by
    have h := Nat.le_ceil ((n : ℝ) / C)
    rw [← hℓ, div_le_iff₀ hCpos] at h
    exact_mod_cast h
  have hℓlt : (ℓ - 1) * C < n := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ n / C by positivity)
    rw [← hℓ] at h
    have h1 : ((ℓ : ℝ) - 1) * C < n := by
      have := (sub_lt_iff_lt_add.mpr h); rw [lt_div_iff₀ hCpos] at this; linarith
    have hℓ1 : 1 ≤ ℓ := by
      by_contra h'; push Not at h'; interval_cases ℓ; simp at hℓC; omega
    have : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by rw [Nat.cast_sub hℓ1]; simp
    exact_mod_cast (show (((ℓ - 1) * C : ℕ) : ℝ) < n by push_cast [this]; linarith)
  have hℓ1 : 1 ≤ ℓ := by
    by_contra h'; push Not at h'; interval_cases ℓ; simp at hℓC; omega
  have hℓn : ℓ ≤ n := by
    have : (ℓ - 1) * 1 ≤ (ℓ - 1) * C := Nat.mul_le_mul_left _ hC
    omega
  -- The tour as a periodic sequence of positions.
  have hlen : L.length = n := by
    have hset : L.toFinset = Finset.univ.erase 0 := by
      ext v; simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun hv h0 => h0L (h0 ▸ hv), hall v⟩
    rw [← List.toFinset_card_of_nodup hnd, hset, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
  set x : ℕ → Fin (n + 1) := fun i => L[i % n]'(by rw [hlen]; exact Nat.mod_lt _ (by omega))
    with hx
  have hxper : ∀ i, x (i + n) = x i := by intro i; simp only [hx, Nat.add_mod_right]
  set w : ℕ → ℝ := fun i => c (x i) (x (i + 1)) with hw
  set r : ℕ → ℝ := fun i => c 0 (x i) with hr
  have hwper : ∀ i, w (i + n) = w i := by
    intro i; simp only [hw, hxper, show i + n + 1 = i + 1 + n by omega]
  have hrper : ∀ i, r (i + n) = r i := by intro i; simp only [hr, hxper]
  -- Rotation `j` of the tour, cut into `ℓ` consecutive blocks of at most `C` customers.
  set e : ℕ → ℕ := fun k => min (k * C) n with he
  have he0 : e 0 = 0 := by simp [he]
  have heℓ : e ℓ = n := by simp only [he]; exact min_eq_right hℓC
  have hek : ∀ k < ℓ, e k = k * C := by
    intro k hk; simp only [he]; apply min_eq_left
    have : k * C ≤ (ℓ - 1) * C := Nat.mul_le_mul_right _ (by omega)
    omega
  have hegap : ∀ k < ℓ, e k < e (k + 1) := by
    intro k hk; rw [hek k hk]; simp only [he]
    have : k * C < n := lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hℓlt
    rw [lt_min_iff]; constructor <;> nlinarith
  have hesize : ∀ k < ℓ, e (k + 1) - e k ≤ C := by
    intro k hk; rw [hek k hk]; simp only [he]
    have := min_le_left ((k + 1) * C) n
    have h1 : (k + 1) * C = k * C + C := by ring
    omega
  set block : ℕ → ℕ → List (Fin (n + 1)) :=
    fun j k => (List.range' (j + e k) (e (k + 1) - e k)).map x with hblock
  set sol : ℕ → List (List (Fin (n + 1))) := fun j => (List.range ℓ).map (block j) with hsol
  have hxmem : ∀ i, x i ∈ L := fun i => List.getElem_mem _
  -- The blocks of rotation `j` concatenate to the rotated tour.
  have hflat : ∀ j < n, (sol j).flatMap id = L.rotate j := by
    intro j hj
    have htel : ∀ K ≤ ℓ, ((List.range K).map (block j)).flatMap id
        = (List.range' j (e K)).map x := by
      intro K hK
      induction K with
      | zero => simp [he0]
      | succ K ih =>
        rw [List.range_succ, List.map_append, List.flatMap_append, ih (by omega)]
        simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, id, hblock, ← List.map_append]
        rw [List.range'_append_1]
        congr 2
        have := hegap K (by omega); omega
    rw [hsol, htel ℓ le_rfl, heℓ]
    apply List.ext_getElem
    · simp [hlen]
    · intro t h1 h2
      simp only [List.getElem_map, List.getElem_range', hx, List.getElem_rotate, hlen, Nat.one_mul]
      congr 1; rw [add_comm j t]
  have hfeas : ∀ j < n, IsVRPSolution C (sol j) := by
    intro j hj
    refine ⟨?_, ?_, ?_⟩
    · intro B hB
      simp only [hsol, List.mem_map, List.mem_range] at hB
      obtain ⟨k, hk, rfl⟩ := hB
      refine ⟨?_, ?_, ?_⟩
      · simp only [hblock, ne_eq, List.map_eq_nil_iff, List.range'_eq_nil_iff]
        have := hegap k hk; omega
      · simp only [hblock, List.length_map, List.length_range']; exact hesize k hk
      · simp only [hblock, List.mem_map]
        rintro ⟨i, -, hi⟩; exact h0L (hi ▸ hxmem i)
    · rw [hflat j hj]; exact List.nodup_rotate.mpr hnd
    · intro v hv; rw [hflat j hj, List.mem_rotate]; exact hall v hv
  -- The cost of rotation `j`.
  have hcost : ∀ j, solutionCost c (sol j)
      = ∑ k ∈ Finset.range ℓ, (r (j + e k) + r (j + e (k + 1) - 1))
        + (∑ i ∈ Finset.range n, w i) - ∑ k ∈ Finset.range ℓ, w (j + e (k + 1) - 1) := by
    intro j
    have hblk : ∀ k < ℓ, routeCost c (block j k)
        = r (j + e k) + r (j + e (k + 1) - 1)
          + (∑ i ∈ Finset.Ico (j + e k) (j + e (k + 1)), w i) - w (j + e (k + 1) - 1) := by
      intro k hk
      have hg := hegap k hk
      obtain ⟨m, hm⟩ : ∃ m, e (k + 1) - e k = m + 1 := ⟨e (k + 1) - e k - 1, by omega⟩
      simp only [hblock, hm]
      rw [routeCost_block, hc.symm _ 0]
      have hend : j + e (k + 1) = j + e k + m + 1 := by omega
      rw [hend, Finset.sum_Ico_succ_top (by omega), Nat.add_sub_cancel]
      simp only [hr, hw]; ring
    rw [solutionCost, hsol, List.map_map]
    rw [show ((List.range ℓ).map (routeCost c ∘ block j)).sum
        = ∑ k ∈ Finset.range ℓ, routeCost c (block j k) by
      rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]; rfl]
    rw [Finset.sum_congr rfl (fun k hk => hblk k (Finset.mem_range.mp hk))]
    have hwin := sum_windows w (fun k => j + e k) ℓ (fun k hk => by have := hegap k hk; omega)
    simp only [he0, Nat.add_zero, heℓ] at hwin
    rw [sum_Ico_period w n hwper j] at hwin
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hwin, Finset.sum_add_distrib]
  -- Averaging over the `n` rotations.
  set Rs := ∑ i ∈ Finset.range n, r i with hRs
  set W := ∑ i ∈ Finset.range n, w i with hW
  have htotal : ∑ j ∈ Finset.range n, solutionCost c (sol j) = 2 * ℓ * Rs + (n - ℓ) * W := by
    simp only [hcost]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_comm,
      Finset.sum_comm (f := fun j k => w (j + e (k + 1) - 1))]
    have h1 : ∀ k ∈ Finset.range ℓ, ∑ j ∈ Finset.range n, (r (j + e k) + r (j + e (k + 1) - 1))
        = 2 * Rs := by
      intro k hk
      have hg := hegap k (Finset.mem_range.mp hk)
      rw [Finset.sum_add_distrib, sum_range_shift r n hrper]
      rw [show ∑ j ∈ Finset.range n, r (j + e (k + 1) - 1)
          = ∑ j ∈ Finset.range n, r (j + (e (k + 1) - 1)) from
        Finset.sum_congr rfl (fun j _ => by congr 1; omega), sum_range_shift r n hrper]
      ring
    have h2 : ∀ k ∈ Finset.range ℓ, ∑ j ∈ Finset.range n, w (j + e (k + 1) - 1) = W := by
      intro k hk
      have hg := hegap k (Finset.mem_range.mp hk)
      rw [show ∑ j ∈ Finset.range n, w (j + e (k + 1) - 1)
          = ∑ j ∈ Finset.range n, w (j + (e (k + 1) - 1)) from
        Finset.sum_congr rfl (fun j _ => by congr 1; omega), sum_range_shift w n hwper]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  -- Identify the averages.
  have hRsum : Rs = ∑ i : Fin (n + 1), c 0 i := by
    have : Rs = (L.map (c 0)).sum := by
      rw [hRs, ← Fin.sum_univ_eq_sum_range, ← List.sum_ofFn]
      congr 1
      apply List.ext_getElem <;> simp [hlen, hr, hx, Nat.mod_eq_of_lt]
    rw [this, ← List.sum_toFinset _ hnd]
    have hset : L.toFinset = Finset.univ.erase 0 := by
      ext v; simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun hv h0 => h0L (h0 ▸ hv), hall v⟩
    rw [hset, Finset.sum_erase _ (hc.refl 0)]
  have hWle : W ≤ routeCost c L := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hLx : L = (List.range' 0 (m + 1)).map x := by
      apply List.ext_getElem
      · simp [hlen, hm]
      · intro t h1 h2; simp [hx, Nat.mod_eq_of_lt (show t < n by omega)]
    have hrc := routeCost_block c x m 0
    rw [← hLx, Nat.zero_add] at hrc
    have hwrap : w m ≤ c (x m) 0 + c 0 (x 0) := by
      have : x (m + 1) = x 0 := by rw [← hm]; simpa using hxper 0
      simp only [hw, this]; exact hc.triangle _ _ _
    have hrange : Finset.range n = Finset.range (m + 1) := by rw [hm]
    rw [hW, hrange, Finset.sum_range_succ, Finset.range_eq_Ico, hrc]
    linarith
  -- Some rotation is at most the average.
  obtain ⟨j, hj, hjle⟩ := Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr (by omega))
    (show ∑ j ∈ Finset.range n, solutionCost c (sol j)
        ≤ ∑ j ∈ Finset.range n, (2 * ℓ * Rs + (n - ℓ) * W) / n by
      rw [htotal, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp; rfl)
  refine ⟨sol j, hfeas j (Finset.mem_range.mp hj), hjle.trans ?_⟩
  have hℓn' : (ℓ : ℝ) ≤ n := by exact_mod_cast hℓn
  rw [avgDepotDist, ← hRsum]
  rw [div_le_iff₀ hnpos]
  have : (n - (ℓ : ℝ)) * W ≤ (n - ℓ) * routeCost c L :=
    mul_le_mul_of_nonneg_left hWle (by linarith)
  field_simp
  nlinarith
