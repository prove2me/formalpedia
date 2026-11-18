-- Prove2me | solution 1 for OWMR.con_engine
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:30.37947+00:00
-- url     : https://prove2.me/submissions/403dc353-9bbf-4c1c-971b-8851e3e60ed7

import Definitions.Def_owmr_consolidation_policy

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

noncomputable section

namespace OWMR.Eng


variable {n : ℕ}

/-- The request after service at cumulative level `U'`, given its ahead volume `a`. -/
def serveElem (batch : Fin n → Bool) (U' : ℝ) (r : Req n) (a : ℝ) : Req n :=
  { r with
    alloc := max 0 (min r.size (U' - a))
    shipped := if batch r.ret = false ∨
        crossesThreshold r.size r.offset r.alloc (max 0 (min r.size (U' - a)))
      then max 0 (min r.size (U' - a)) else r.shipped }

/-- Map along a list with the running ahead volume. -/
def mapAh {β : Type} (f : Req n → ℝ → β) : List (Req n) → ℝ → List β
  | [], _ => []
  | r :: rs, a => f r a :: mapAh f rs (a + r.size)

/-- Allocations consecutive in the queue at cumulative level `U`, the head having ahead `a`. -/
def ContigA : List (Req n) → ℝ → ℝ → Prop
  | [], _, _ => True
  | r :: rs, a, U => 0 ≤ r.size ∧ r.alloc = max 0 (min r.size (U - a)) ∧ ContigA rs (a + r.size) U

lemma ContigA.sizes_nonneg : ∀ {l : List (Req n)} {a U : ℝ}, ContigA l a U → ∀ r ∈ l, 0 ≤ r.size
  | [], _, _, _ => by simp
  | r :: rs, a, U, h => by
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact h.1
    · exact ContigA.sizes_nonneg h.2.2 r' hr'

lemma sum_sizes_nonneg (l : List (Req n)) (h : ∀ r ∈ l, 0 ≤ r.size) :
    0 ≤ (l.map Req.size).sum :=
  List.sum_nonneg (by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact h r hr)

/-- Below the ahead of the head, the level does not matter. -/
lemma ContigA.low : ∀ {l : List (Req n)} {a U V : ℝ}, ContigA l a U → U ≤ a → V ≤ a →
    ContigA l a V
  | [], _, _, _, _, _, _ => trivial
  | r :: rs, a, U, V, h, hU, hV => by
    obtain ⟨h0, h1, h2⟩ := h
    refine ⟨h0, ?_, ContigA.low h2 (by linarith) (by linarith)⟩
    rw [h1, max_eq_left (min_le_of_right_le (by linarith)),
      max_eq_left (min_le_of_right_le (by linarith))]

lemma mapAh_serveElem_max (batch : Fin n → Bool) :
    ∀ (l : List (Req n)) (b L : ℝ), (∀ r ∈ l, 0 ≤ r.size) →
      mapAh (serveElem batch L) l b = mapAh (serveElem batch (max L b)) l b
  | [], _, _, _ => rfl
  | r :: rs, b, L, hs => by
    have hr := hs r List.mem_cons_self
    have hrs : ∀ r ∈ rs, 0 ≤ r.size := fun r' h => hs r' (List.mem_cons_of_mem _ h)
    simp only [mapAh]
    have e : max 0 (min r.size (L - b)) = max 0 (min r.size (max L b - b)) := by
      rcases le_total L b with h | h
      · rw [max_eq_right h, sub_self, max_eq_left (min_le_of_right_le (by linarith)),
          min_eq_right hr, max_self]
      · rw [max_eq_left h]
    congr 1
    · simp only [serveElem, e]
    · rw [mapAh_serveElem_max batch rs (b + r.size) L hrs,
        mapAh_serveElem_max batch rs (b + r.size) (max L b) hrs]
      congr 2
      rw [max_assoc, max_eq_right (by linarith : b ≤ b + r.size)]

lemma serve_cons' (batch : Fin n → Bool) (r : Req n) (rs : List (Req n)) (w : ℝ) :
    serve batch (r :: rs) w =
      ({ r with
          alloc := r.alloc + min (r.size - r.alloc) w
          shipped := if batch r.ret = false ∨
              crossesThreshold r.size r.offset r.alloc (r.alloc + min (r.size - r.alloc) w)
            then r.alloc + min (r.size - r.alloc) w else r.shipped }
        :: (serve batch rs (w - min (r.size - r.alloc) w)).1,
        (serve batch rs (w - min (r.size - r.alloc) w)).2.1,
        (serve batch rs (w - min (r.size - r.alloc) w)).2.2
          + Pi.single r.ret ((if batch r.ret = false ∨
              crossesThreshold r.size r.offset r.alloc (r.alloc + min (r.size - r.alloc) w)
            then r.alloc + min (r.size - r.alloc) w else r.shipped) - r.shipped)) := by
  simp only [serve]
  split_ifs with h
  · congr 3; ring
  · simp

/-- FIFO service of a consecutive queue: `serve` raises the cumulative level by `w`. -/
lemma serve_contig (batch : Fin n → Bool) :
    ∀ (l : List (Req n)) (a U w : ℝ), a ≤ U → U ≤ a + (l.map Req.size).sum → 0 ≤ w →
      ContigA l a U →
      (serve batch l w).1 = mapAh (serveElem batch (U + w)) l a ∧
      (serve batch l w).2.1 = max 0 (U + w - (a + (l.map Req.size).sum)) ∧
      (serve batch l w).2.2 = (mapAh (fun r a' =>
        Pi.single r.ret ((serveElem batch (U + w) r a').shipped - r.shipped)) l a).sum
  | [], a, U, w, haU, hUa, hw, _ => by
    have : U = a := le_antisymm (by simpa using hUa) haU
    subst this
    simp [serve, mapAh, max_eq_right hw]
  | r :: rs, a, U, w, haU, hUa, hw, h => by
    obtain ⟨hr0, hra, hrs⟩ := h
    have hsz := ContigA.sizes_nonneg hrs
    have hsum := sum_sizes_nonneg rs hsz
    simp only [List.map_cons, List.sum_cons] at hUa
    -- the allocation of the head
    have hal : r.alloc = min r.size (U - a) := by
      rw [hra, max_eq_right (le_min hr0 (by linarith))]
    have hnew : r.alloc + min (r.size - r.alloc) w = max 0 (min r.size (U + w - a)) := by
      rw [max_eq_right (le_min hr0 (by linarith)), hal]
      rcases le_total (U - a) r.size with h1 | h1
      · rw [min_eq_right h1]
        rcases le_total (r.size - (U - a)) w with h2 | h2
        · rw [min_eq_left h2, min_eq_left (by linarith)]; ring
        · rw [min_eq_right h2, min_eq_right (by linarith)]; ring
      · rw [min_eq_left h1, sub_self, min_eq_left hw, add_zero, min_eq_left (by linarith)]
    -- the rest of the queue sees the level `max U (a + size)`
    have hrs' : ContigA rs (a + r.size) (max U (a + r.size)) := by
      rcases le_total U (a + r.size) with h1 | h1
      · rw [max_eq_right h1]
        exact ContigA.low hrs h1 le_rfl
      · rw [max_eq_left h1]; exact hrs
    have hw' : 0 ≤ w - min (r.size - r.alloc) w := by
      linarith [min_le_right (r.size - r.alloc) w]
    have hlev : max U (a + r.size) + (w - min (r.size - r.alloc) w) = max (U + w) (a + r.size) := by
      rcases le_total U (a + r.size) with h1 | h1
      · have hal' : r.alloc = U - a := by rw [hal]; exact min_eq_right (by linarith)
        rw [max_eq_right h1, hal']
        rcases le_total (r.size - (U - a)) w with h2 | h2
        · rw [min_eq_left h2, max_eq_left (by linarith)]; ring
        · rw [min_eq_right h2, max_eq_right (by linarith)]; ring
      · have hal' : r.alloc = r.size := by rw [hal]; exact min_eq_left (by linarith)
        rw [max_eq_left h1, hal', sub_self, min_eq_left hw, max_eq_left (by linarith)]
        ring
    obtain ⟨ih1, ih2, ih3⟩ := serve_contig batch rs (a + r.size) (max U (a + r.size))
      (w - min (r.size - r.alloc) w) (le_max_right _ _)
      (max_le (by linarith) (by linarith)) hw' hrs'
    rw [hlev] at ih1 ih2 ih3
    have hm := mapAh_serveElem_max batch rs (a + r.size) (U + w) hsz
    rw [serve_cons']
    refine ⟨?_, ?_, ?_⟩
    · simp only [mapAh]
      rw [ih1, ← hm, hnew]
      rfl
    · simp only [List.map_cons, List.sum_cons]
      rw [ih2]
      rcases le_total (U + w) (a + r.size) with h1 | h1
      · rw [max_eq_right h1, max_eq_left (by linarith), max_eq_left (by linarith)]
      · rw [max_eq_left h1]; ring_nf
    · simp only [mapAh, List.sum_cons]
      rw [ih3, add_comm, hnew]
      congr 1
      -- the ship amounts of the rest are unchanged by raising the level below `a + size`
      have key : ∀ (l : List (Req n)) (b' : ℝ), a + r.size ≤ b' → (∀ y ∈ l, 0 ≤ y.size) →
          mapAh (fun y a' => (Pi.single y.ret
            ((serveElem batch (max (U + w) (a + r.size)) y a').shipped - y.shipped) : Fin n → ℝ)) l b'
          = mapAh (fun y a' => (Pi.single y.ret
            ((serveElem batch (U + w) y a').shipped - y.shipped) : Fin n → ℝ)) l b' := by
        intro l
        induction l with
        | nil => intro _ _ _; rfl
        | cons r' rs' ih =>
          intro b' hb' hs'
          have hr' := hs' r' List.mem_cons_self
          simp only [mapAh]
          rw [ih (b' + r'.size) (by linarith) (fun x hx => hs' x (List.mem_cons_of_mem _ hx))]
          congr 1
          have e : max 0 (min r'.size (max (U + w) (a + r.size) - b'))
              = max 0 (min r'.size (U + w - b')) := by
            rcases le_total (U + w) (a + r.size) with h | h
            · rw [max_eq_right h, max_eq_left (min_le_of_right_le (by linarith)),
                max_eq_left (min_le_of_right_le (by linarith))]
            · rw [max_eq_left h]
          simp only [serveElem, e]
      rw [key rs (a + r.size) le_rfl hsz]



/-- `g` gives the running ahead volume along the list, starting from `a`, with sizes `sz`. -/
def RunAh {α : Type} (g sz : α → ℝ) : List α → ℝ → Prop
  | [], _ => True
  | k :: ks, a => g k = a ∧ RunAh g sz ks (a + sz k)

section runah

variable {α : Type} (g sz : α → ℝ)

lemma RunAh_append : ∀ (l1 l2 : List α) (a : ℝ),
    RunAh g sz (l1 ++ l2) a ↔ RunAh g sz l1 a ∧ RunAh g sz l2 (a + (l1.map sz).sum)
  | [], l2, a => by simp [RunAh]
  | k :: ks, l2, a => by
    simp only [List.cons_append, RunAh, List.map_cons, List.sum_cons]
    rw [RunAh_append ks l2 (a + sz k), add_assoc]
    tauto

lemma RunAh_congr {g' sz' : α → ℝ} : ∀ (l : List α) (a : ℝ), (∀ k ∈ l, g k = g' k) →
    (∀ k ∈ l, sz k = sz' k) → (RunAh g sz l a ↔ RunAh g' sz' l a)
  | [], _, _, _ => by simp [RunAh]
  | k :: ks, a, hg, hs => by
    simp only [RunAh]
    rw [hg k List.mem_cons_self, hs k List.mem_cons_self,
      RunAh_congr ks (a + sz' k) (fun k' h => hg k' (List.mem_cons_of_mem _ h))
        (fun k' h => hs k' (List.mem_cons_of_mem _ h))]

lemma RunAh_map {β : Type} (f : β → α) : ∀ (l : List β) (a : ℝ),
    RunAh g sz (l.map f) a ↔ RunAh (g ∘ f) (sz ∘ f) l a
  | [], _ => by simp [RunAh]
  | k :: ks, a => by
    simp only [List.map_cons, RunAh, Function.comp]
    rw [RunAh_map f ks]

lemma RunAh.pairwise : ∀ {l : List α} {a : ℝ}, RunAh g sz l a → (∀ k ∈ l, 0 ≤ sz k) →
    l.Pairwise (fun k k' => g k + sz k ≤ g k') ∧ ∀ k ∈ l, a ≤ g k
  | [], _, _, _ => by simp
  | k :: ks, a, h, hs => by
    obtain ⟨h1, h2⟩ := h
    have hks : ∀ k' ∈ ks, 0 ≤ sz k' := fun k' hk' => hs k' (List.mem_cons_of_mem _ hk')
    obtain ⟨ih1, ih2⟩ := RunAh.pairwise h2 hks
    refine ⟨List.pairwise_cons.2 ⟨fun k' hk' => by rw [h1]; exact ih2 k' hk', ih1⟩, ?_⟩
    intro k' hk'
    rcases List.mem_cons.1 hk' with rfl | hk'
    · rw [h1]
    · linarith [ih2 k' hk', hs k List.mem_cons_self]

lemma RunAh_dropWhile (p : α → Bool) : ∀ (l : List α) (a : ℝ), RunAh g sz l a →
    RunAh g sz (l.dropWhile p) (a + ((l.takeWhile p).map sz).sum)
  | [], a, _ => by simp [RunAh]
  | k :: ks, a, h => by
    obtain ⟨h1, h2⟩ := h
    by_cases hp : p k = true
    · simp only [List.dropWhile_cons_of_pos hp, List.takeWhile_cons_of_pos hp, List.map_cons,
        List.sum_cons]
      have := RunAh_dropWhile p ks (a + sz k) h2
      rwa [add_assoc] at this
    · rw [List.dropWhile_cons_of_neg hp, List.takeWhile_cons_of_neg hp]
      simp only [List.map_nil, List.sum_nil, add_zero]
      exact ⟨h1, h2⟩

/-- Along the dropped prefix, an upper bound for the running ends persists. -/
lemma RunAh_takeWhile_le (p : α → Bool) (V : ℝ) : ∀ (l : List α) (a : ℝ), RunAh g sz l a →
    a ≤ V → (∀ k ∈ l, p k = true → g k + sz k ≤ V) →
    a + ((l.takeWhile p).map sz).sum ≤ V
  | [], a, _, ha, _ => by simpa using ha
  | k :: ks, a, h, ha, hV => by
    obtain ⟨h1, h2⟩ := h
    by_cases hp : p k = true
    · simp only [List.takeWhile_cons_of_pos hp, List.map_cons, List.sum_cons]
      have hk := hV k List.mem_cons_self hp
      have := RunAh_takeWhile_le p V ks (a + sz k) h2 (by rw [← h1]; exact hk)
        (fun k' hk' => hV k' (List.mem_cons_of_mem _ hk'))
      linarith
    · rw [List.takeWhile_cons_of_neg hp]
      simpa using ha

end runah

lemma filter_eq_dropWhile {α : Type} (p : α → Bool) : ∀ (l : List α),
    l.Pairwise (fun a b => p a = true → p b = true) → l.filter p = l.dropWhile (fun a => !p a)
  | [], _ => rfl
  | k :: ks, h => by
    rw [List.pairwise_cons] at h
    by_cases hp : p k = true
    · rw [List.filter_cons_of_pos hp, List.dropWhile_cons_of_neg (by simp [hp])]
      congr 1
      exact List.filter_eq_self.2 fun b hb => h.1 b hb hp
    · rw [List.filter_cons_of_neg hp, List.dropWhile_cons_of_pos (by simpa using hp)]
      exact filter_eq_dropWhile p ks h.2

/-- Running sums along the retailers with positive requests, in index order. -/
lemma RunAh_finRange : ∀ (m : ℕ) (f : Fin m → ℝ) (b : ℝ), (∀ i, 0 ≤ f i) →
    RunAh (fun i => b + ∑ j ∈ Finset.univ.filter (· < i), f j) f
      ((List.finRange m).filter (fun i => decide (0 < f i))) b
  | 0, f, b, _ => by simp [RunAh]
  | m + 1, f, b, hf => by
    have hsum : ∀ i : Fin m, ∑ j ∈ Finset.univ.filter (· < i.succ), f j
        = f 0 + ∑ j ∈ Finset.univ.filter (· < i), f j.succ := by
      intro i
      rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
      simp [Fin.succ_lt_succ_iff, Fin.succ_pos]
    have ih := RunAh_finRange m (fun i => f i.succ) (b + f 0) (fun i => hf _)
    rw [List.finRange_succ, List.filter_cons, List.filter_map]
    by_cases h0 : 0 < f 0
    · simp only [h0, decide_true, if_true, RunAh]
      refine ⟨by simp, ?_⟩
      rw [RunAh_map]
      refine (RunAh_congr _ _ _ _ (fun k _ => ?_) (fun k _ => rfl)).1 ih
      simp only [Function.comp, hsum]
      ring
    · have hf0 : f 0 = 0 := le_antisymm (not_lt.1 h0) (hf 0)
      simp only [h0, decide_false, Bool.false_eq_true, if_false]
      rw [RunAh_map]
      rw [hf0, add_zero] at ih
      refine (RunAh_congr _ _ _ _ (fun k _ => ?_) (fun k _ => rfl)).1 ih
      simp only [Function.comp, hsum, hf0, zero_add]



variable {n : ℕ}

/-- Volume of all requests created before period `s`. -/
def Pq (q : ℕ → Fin n → ℝ) (s : ℕ) : ℝ := ∑ r ∈ Finset.range s, ∑ j, q r j

/-- Volume ahead of request `(s,i)`. -/
def ahx (q : ℕ → Fin n → ℝ) (s : ℕ) (i : Fin n) : ℝ :=
  Pq q s + ∑ j ∈ Finset.univ.filter (· < i), q s j

/-- Requests created in period `s`, in retailer order. -/
def perL (q : ℕ → Fin n → ℝ) (s : ℕ) : List (ℕ × Fin n) :=
  ((List.finRange n).filter (fun i => decide (0 < q s i))).map (fun i => (s, i))

/-- All requests created through period `t`, in creation order. -/
def Lall (q : ℕ → Fin n → ℝ) (t : ℕ) : List (ℕ × Fin n) :=
  (List.range (t + 1)).flatMap (perL q)

section lists

variable (q : ℕ → Fin n → ℝ) (hq : ∀ s i, 0 ≤ q s i)
include hq

omit hq in
lemma Lall_zero : Lall q 0 = perL q 0 := by simp [Lall]

omit hq in
lemma Lall_succ (t : ℕ) : Lall q (t + 1) = Lall q t ++ perL q (t + 1) := by
  simp [Lall, List.range_succ, List.flatMap_append]

omit hq in
lemma mem_perL (s : ℕ) (k : ℕ × Fin n) : k ∈ perL q s ↔ k.1 = s ∧ 0 < q s k.2 := by
  obtain ⟨a, b⟩ := k
  simp only [perL, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩; exact ⟨rfl, hi⟩
  · rintro ⟨rfl, h⟩; exact ⟨b, h, rfl, rfl⟩

omit hq in
lemma mem_Lall (t : ℕ) (k : ℕ × Fin n) : k ∈ Lall q t ↔ k.1 ≤ t ∧ 0 < q k.1 k.2 := by
  simp only [Lall, List.mem_flatMap, List.mem_range, mem_perL]
  constructor
  · rintro ⟨s, hs, rfl, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨h1, h2⟩; exact ⟨k.1, by omega, rfl, h2⟩

omit hq in
lemma sum_map_filter_ite {β : Type} (l : List β) (p : β → Bool) (f : β → ℝ) :
    ((l.filter p).map f).sum = (l.map (fun j => if p j then f j else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

lemma sum_perL (s : ℕ) : ((perL q s).map (fun k => q k.1 k.2)).sum = ∑ j, q s j := by
  simp only [perL, List.map_map]
  rw [show ((fun k : ℕ × Fin n => q k.1 k.2) ∘ fun i => (s, i)) = q s from rfl,
    sum_map_filter_ite, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : 0 < q s j
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    exact (le_antisymm (not_lt.1 h) (hq s j)).symm

lemma sum_Lall (t : ℕ) : ((Lall q t).map (fun k => q k.1 k.2)).sum = Pq q (t + 1) := by
  induction t with
  | zero => simp [Lall_zero q, sum_perL q hq, Pq]
  | succ t ih =>
    rw [Lall_succ q, List.map_append, List.sum_append, ih, sum_perL q hq, Pq, Pq,
      Finset.sum_range_succ _ (t + 1)]

lemma RunAh_perL (s : ℕ) :
    RunAh (fun k => ahx q k.1 k.2) (fun k => q k.1 k.2) (perL q s) (Pq q s) := by
  unfold perL
  rw [RunAh_map]
  exact RunAh_finRange n (q s) (Pq q s) (hq s)

lemma RunAh_Lall (t : ℕ) :
    RunAh (fun k => ahx q k.1 k.2) (fun k => q k.1 k.2) (Lall q t) 0 := by
  induction t with
  | zero =>
    rw [Lall_zero q]
    have := RunAh_perL q hq 0
    simpa [Pq] using this
  | succ t ih =>
    rw [Lall_succ q, RunAh_append]
    refine ⟨ih, ?_⟩
    rw [zero_add, sum_Lall q hq]
    exact RunAh_perL q hq (t + 1)

omit hq in
lemma ahx_nonneg (hq : ∀ s i, 0 ≤ q s i) (s : ℕ) (i : Fin n) : Pq q s ≤ ahx q s i :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hq s j)

lemma ahx_add_le (s : ℕ) (i : Fin n) : ahx q s i + q s i ≤ Pq q (s + 1) := by
  simp only [ahx, Pq]
  rw [Finset.sum_range_succ, add_assoc]
  refine add_le_add le_rfl ?_
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < i)]
  refine add_le_add le_rfl ?_
  rw [← Finset.add_sum_erase _ _ (by simp : i ∈ Finset.univ.filter (fun j => ¬ j < i))]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hq s j)

lemma Pq_mono {s s' : ℕ} (h : s ≤ s') : Pq q s ≤ Pq q s' := by
  unfold Pq
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    fun r _ _ => Finset.sum_nonneg fun j _ => hq r j

lemma Lall_pairwise (t : ℕ) :
    (Lall q t).Pairwise (fun k k' => ahx q k.1 k.2 + q k.1 k.2 ≤ ahx q k'.1 k'.2) :=
  (RunAh.pairwise _ _ (RunAh_Lall q hq t) (fun k _ => hq _ _)).1

/-- Requests later in the list are created no earlier. -/
lemma Lall_pairwise_born (t : ℕ) : (Lall q t).Pairwise (fun k k' => k.1 ≤ k'.1) := by
  refine (Lall_pairwise q hq t).imp_of_mem fun {k k'} hk hk' h => ?_
  rw [mem_Lall] at hk hk'
  by_contra hlt
  rw [not_le] at hlt
  have h1 := ahx_add_le q hq k'.1 k'.2
  have h2 := Pq_mono q hq (show k'.1 + 1 ≤ k.1 by omega)
  have h3 := ahx_nonneg q hq k.1 k.2
  linarith [hk.2, hk'.2]

lemma Lall_nodup (t : ℕ) : (Lall q t).Nodup := by
  refine (Lall_pairwise q hq t).imp_of_mem fun {k k'} hk _ h => ?_
  rw [mem_Lall] at hk
  intro hkk
  subst hkk
  linarith [hk.2]

end lists



variable {n : ℕ}

/-- The supplier position computed in step 2 of a period. -/
def posE (L0 : ℕ) (L : Fin n → ℕ) (S : Fin n → ℝ) (st : EngState n) (t : ℕ) : ℝ :=
  st.Wbar + ∑ i, reserve st i + supInTransit L0 st t + ∑ i, (physPos L st t i - S i)

lemma sum_map_add_list {β : Type} (l : List β) (f g : β → ℝ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

lemma sum_map_sub_list {β : Type} (l : List β) (f g : β → ℝ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

lemma sum_map_filter_ite' {β : Type} (l : List β) (p : β → Bool) (f : β → ℝ) :
    ((l.filter p).map f).sum = (l.map (fun j => if p j then f j else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-- Per-retailer queue terms. -/
def qterm (l : List (Req n)) (i : Fin n) (f : Req n → ℝ) : ℝ :=
  ((l.filter (fun r => r.ret = i)).map f).sum

lemma unalloc_add_reserve (st : EngState n) (i : Fin n) :
    unalloc st i + reserve st i = qterm st.queue i (fun r => r.size - r.shipped) := by
  unfold unalloc reserve qterm
  rw [← sum_map_add_list]
  congr 1
  apply List.map_congr_left
  intro r _
  ring

lemma phat_eq (L : Fin n → ℕ) (st : EngState n) (t : ℕ) (i : Fin n) :
    phat L st t i = physPos L st t i + qterm st.queue i (fun r => r.size - r.shipped) := by
  unfold phat
  rw [add_assoc, unalloc_add_reserve]

/-- Summing a per-retailer queue term over all retailers. -/
lemma sum_qterm (l : List (Req n)) (f : Req n → ℝ) :
    ∑ i, qterm l i f = (l.map f).sum := by
  unfold qterm
  simp_rw [sum_map_filter_ite']
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]
    congr 1
    simp

lemma sum_reserve (st : EngState n) :
    ∑ i, reserve st i = (st.queue.map (fun r => r.alloc - r.shipped)).sum := by
  rw [← sum_qterm]
  rfl

/-! ### `sendOut` -/

lemma physPos_sendOut (L : Fin n → ℕ) (t : ℕ) (qv : Fin n → ℝ) (st : EngState n) (i : Fin n) :
    physPos L (sendOut L t qv st) t i = physPos L st t i + qv i := by
  unfold physPos inTransit sendOut
  dsimp only
  by_cases hL : L i = 0
  · simp [hL]
  · simp only [hL, if_false]
    have hmem : L i - 1 ∈ Finset.range (L i) := Finset.mem_range.2 (by omega)
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
    have e1 : t + 1 + (L i - 1) = t + L i := by omega
    rw [e1, Function.update_self]
    have e2 : ∑ x ∈ (Finset.range (L i)).erase (L i - 1),
        Function.update (st.retPipe i) (t + L i) (st.retPipe i (t + L i) + qv i) (t + 1 + x)
        = ∑ x ∈ (Finset.range (L i)).erase (L i - 1), st.retPipe i (t + 1 + x) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Function.update_of_ne]
      have := Finset.ne_of_mem_erase hk
      omega
    rw [e2]
    ring

@[simp] lemma sendOut_queue (L : Fin n → ℕ) (t : ℕ) (qv : Fin n → ℝ) (st : EngState n) :
    (sendOut L t qv st).queue = st.queue := rfl
@[simp] lemma sendOut_Wbar (L : Fin n → ℕ) (t : ℕ) (qv : Fin n → ℝ) (st : EngState n) :
    (sendOut L t qv st).Wbar = st.Wbar := rfl
@[simp] lemma sendOut_supPipe (L : Fin n → ℕ) (t : ℕ) (qv : Fin n → ℝ) (st : EngState n) :
    (sendOut L t qv st).supPipe = st.supPipe := rfl
@[simp] lemma sendOut_nOrd (L : Fin n → ℕ) (t : ℕ) (qv : Fin n → ℝ) (st : EngState n) :
    (sendOut L t qv st).nOrd = st.nOrd := rfl
@[simp] lemma sendOut_running (L : Fin n → ℕ) (t : ℕ) (qv : Fin n → ℝ) (st : EngState n) :
    (sendOut L t qv st).running = st.running := rfl

lemma sendOut_retPipe_far (L : Fin n → ℕ) (t : ℕ) (qv : Fin n → ℝ) (st : EngState n) (i : Fin n)
    (r : ℕ) (hr : t + L i < r) : (sendOut L t qv st).retPipe i r = st.retPipe i r := by
  unfold sendOut
  dsimp only
  split_ifs
  · rfl
  · rw [Function.update_of_ne (by omega)]

/-! ### `receive` and `applyDemand` -/

lemma physPos_receive (L : Fin n → ℕ) (st : EngState n) (t : ℕ) (i : Fin n) :
    physPos L (receive st (t + 1)) (t + 1) i = physPos L st t i + st.retPipe i (t + 1 + L i) := by
  unfold physPos inTransit receive
  dsimp only
  have h1 := Finset.sum_range_succ (fun k => st.retPipe i (t + 1 + k)) (L i)
  have h2 := Finset.sum_range_succ' (fun k => st.retPipe i (t + 1 + k)) (L i)
  have e : ∑ k ∈ Finset.range (L i), st.retPipe i (t + 1 + (k + 1))
      = ∑ k ∈ Finset.range (L i), st.retPipe i (t + 1 + 1 + k) :=
    Finset.sum_congr rfl fun k _ => by congr 1; omega
  rw [e, add_zero] at h2
  linarith

lemma supInTransit_receive (L0 : ℕ) (st : EngState n) (t : ℕ) :
    (receive st (t + 1)).Wbar + supInTransit L0 (receive st (t + 1)) (t + 1)
      = st.Wbar + supInTransit L0 st t + st.supPipe (t + 1 + L0) := by
  unfold supInTransit receive
  dsimp only
  have h1 := Finset.sum_range_succ (fun k => st.supPipe (t + 1 + k)) L0
  have h2 := Finset.sum_range_succ' (fun k => st.supPipe (t + 1 + k)) L0
  have e : ∑ k ∈ Finset.range L0, st.supPipe (t + 1 + (k + 1))
      = ∑ k ∈ Finset.range L0, st.supPipe (t + 1 + 1 + k) :=
    Finset.sum_congr rfl fun k _ => by congr 1; omega
  rw [e, add_zero] at h2
  linarith

@[simp] lemma receive_queue (st : EngState n) (t : ℕ) : (receive st t).queue = st.queue := rfl
@[simp] lemma receive_retPipe (st : EngState n) (t : ℕ) : (receive st t).retPipe = st.retPipe := rfl
@[simp] lemma receive_supPipe (st : EngState n) (t : ℕ) : (receive st t).supPipe = st.supPipe := rfl
@[simp] lemma receive_nOrd (st : EngState n) (t : ℕ) : (receive st t).nOrd = st.nOrd := rfl
@[simp] lemma receive_running (st : EngState n) (t : ℕ) : (receive st t).running = st.running := rfl
@[simp] lemma receive_Wbar (st : EngState n) (t : ℕ) :
    (receive st t).Wbar = st.Wbar + st.supPipe t := rfl
@[simp] lemma applyDemand_queue (st : EngState n) (dt : DemandVec n) :
    (applyDemand st dt).queue = st.queue := rfl
@[simp] lemma applyDemand_retPipe (st : EngState n) (dt : DemandVec n) :
    (applyDemand st dt).retPipe = st.retPipe := rfl
@[simp] lemma applyDemand_supPipe (st : EngState n) (dt : DemandVec n) :
    (applyDemand st dt).supPipe = st.supPipe := rfl
@[simp] lemma applyDemand_Wbar (st : EngState n) (dt : DemandVec n) :
    (applyDemand st dt).Wbar = st.Wbar := rfl
@[simp] lemma applyDemand_nOrd (st : EngState n) (dt : DemandVec n) :
    (applyDemand st dt).nOrd = st.nOrd := rfl
@[simp] lemma applyDemand_running (st : EngState n) (dt : DemandVec n) :
    (applyDemand st dt).running = st.running := rfl

lemma physPos_applyDemand (L : Fin n → ℕ) (st : EngState n) (dt : DemandVec n) (t : ℕ)
    (i : Fin n) : physPos L (applyDemand st dt) t i = physPos L st t i - (dt i : ℝ) := by
  unfold physPos applyDemand inTransit
  dsimp only
  ring

lemma posE_receive (L0 : ℕ) (L : Fin n → ℕ) (S : Fin n → ℝ) (st : EngState n) (t : ℕ)
    (h0 : st.supPipe (t + 1 + L0) = 0) (hr : ∀ i, st.retPipe i (t + 1 + L i) = 0) :
    posE L0 L S (receive st (t + 1)) (t + 1) = posE L0 L S st t := by
  unfold posE
  have e1 := supInTransit_receive L0 st t
  have e2 : ∀ i, physPos L (receive st (t + 1)) (t + 1) i = physPos L st t i := fun i => by
    rw [physPos_receive, hr i, add_zero]
  simp only [e2]
  have e3 : ∑ i, reserve (receive st (t + 1)) i = ∑ i, reserve st i := rfl
  rw [e3]
  linarith

lemma posE_applyDemand (L0 : ℕ) (L : Fin n → ℕ) (S : Fin n → ℝ) (st : EngState n)
    (dt : DemandVec n) (t : ℕ) :
    posE L0 L S (applyDemand st dt) t = posE L0 L S st t - ∑ i, (dt i : ℝ) := by
  unfold posE
  simp only [physPos_applyDemand]
  have e3 : ∑ i, reserve (applyDemand st dt) i = ∑ i, reserve st i := rfl
  have e4 : supInTransit L0 (applyDemand st dt) t = supInTransit L0 st t := rfl
  rw [e3, e4, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [applyDemand_Wbar]
  ring

lemma phat_receive (L : Fin n → ℕ) (st : EngState n) (t : ℕ) (i : Fin n)
    (hr : st.retPipe i (t + 1 + L i) = 0) :
    phat L (receive st (t + 1)) (t + 1) i = phat L st t i := by
  rw [phat_eq, phat_eq, physPos_receive, hr, add_zero]
  rfl

lemma phat_applyDemand (L : Fin n → ℕ) (st : EngState n) (dt : DemandVec n) (t : ℕ) (i : Fin n) :
    phat L (applyDemand st dt) t i = phat L st t i - (dt i : ℝ) := by
  rw [phat_eq, phat_eq, physPos_applyDemand]
  simp only [applyDemand_queue]
  ring


end OWMR.Eng


/-! Engine lemmas, part 5: the explicit run data and the generic period step. -/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR


namespace OWMR.Eng

variable {n : ℕ}

lemma map_mapIdx_const {α β γ : Type} (g : β → γ) (h : α → γ) :
    ∀ (l : List α) (f : ℕ → α → β), (∀ k a, g (f k a) = h a) → (l.mapIdx f).map g = l.map h
  | [], _, _ => rfl
  | a :: l, f, hf => by
    rw [List.mapIdx_cons, List.map_cons, List.map_cons, hf]
    rw [map_mapIdx_const g h l (fun i => f (i + 1)) (fun k a => hf (k + 1) a)]

lemma mem_mapIdx_prop {α β : Type} (P : β → Prop) (l : List α) (f : ℕ → α → β)
    (hf : ∀ k a, a ∈ l → P (f k a)) : ∀ b ∈ l.mapIdx f, P b := by
  intro b hb
  obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.1 hb
  exact hf k _ (List.getElem_mem hk)

/-- The request key. -/
def key (r : Req n) : ℕ × Fin n := (r.born, r.ret)

section explicit

variable (N : Network n) (c : ConChoice n) (act : (ℕ → DemandVec n) → ℕ → Prop)
  [∀ d, DecidablePred (act d)] (Yp : (ℕ → DemandVec n) → ℕ → ℝ)
  (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ) (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)

/-- Supplier order. -/
def q0x (d : ℕ → DemandVec n) (t : ℕ) : ℝ := if act d t ∧ Yp d t ≤ c.s0 then c.S0 - Yp d t else 0

/-- Cumulative supply received through period `t`. -/
def Vx (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (t + 1 - N.L0), q0x c act Yp d r

/-- Supplier position after the order. -/
def Ypost (d : ℕ → DemandVec n) (t : ℕ) : ℝ := if Yp d t ≤ c.s0 then c.S0 else Yp d t

/-- Number of ordinary requests created through period `t`. -/
def nOx (d : ℕ → DemandVec n) (t : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (t + 1), if 0 < r ∧ act d (r - 1) then
    ((List.finRange n).filter (fun j => decide (0 < q d r j))).length else 0

/-- Requests pending after the allocation of period `t - 1`, or created in period `t`. -/
def Lpre (d : ℕ → DemandVec n) (t : ℕ) : List (ℕ × Fin n) :=
  (Lall (q d) t).filter (fun k => decide (k.1 = t ∨
    Vx N c act Yp d (t - 1) < ahx (q d) k.1 k.2 + q d k.1 k.2))

/-- The projected invariant of a state after step 2 (requests and the supplier order) of a running
period `t`. -/
structure InvP (d : ℕ → DemandVec n) (t : ℕ) (Z : EngState n) : Prop where
  wbar : Z.Wbar = max (Vx N c act Yp d (t - 1) - Pq (q d) t) 0
    + (Vx N c act Yp d t - Vx N c act Yp d (t - 1))
  sup : ∀ r, t < r → Z.supPipe r =
    if 0 < N.L0 ∧ r ≤ t + N.L0 then q0x c act Yp d (r - N.L0) else 0
  keys : Z.queue.map key = Lpre N c act Yp q d t
  elems : ∀ r ∈ Z.queue, r.size = q d r.born r.ret ∧
    r.alloc = max 0 (min r.size (min (Vx N c act Yp d (t - 1)) (Pq (q d) t)
      - ahx (q d) r.born r.ret)) ∧ 0 ≤ r.shipped ∧ r.shipped ≤ r.alloc
  phat : ∀ i, phat N.L Z t i = Ph d t i
  ret : ∀ i r, t + N.L i < r → Z.retPipe i r = 0
  nord : Z.nOrd = nOx act q d t
  pos : posE N.L0 N.L c.S Z t = Ypost c Yp d t

end explicit


/-! ### Generic facts about lists of requests -/

lemma ContigA_of_RunAh (g : Req n → ℝ) (U : ℝ) : ∀ (l : List (Req n)) (a : ℝ),
    RunAh g Req.size l a → (∀ r ∈ l, 0 ≤ r.size ∧ r.alloc = max 0 (min r.size (U - g r))) →
    ContigA l a U
  | [], _, _, _ => trivial
  | r :: rs, a, h, he => by
    obtain ⟨h1, h2⟩ := h
    have hr := he r List.mem_cons_self
    refine ⟨hr.1, by rw [hr.2, h1], ContigA_of_RunAh g U rs (a + r.size) h2
      (fun r' h' => he r' (List.mem_cons_of_mem _ h'))⟩

lemma mapAh_eq_map {β : Type} (g : Req n → ℝ) (f : Req n → ℝ → β) : ∀ (l : List (Req n)) (a : ℝ),
    RunAh g Req.size l a → mapAh f l a = l.map (fun r => f r (g r))
  | [], _, _ => rfl
  | r :: rs, a, h => by
    obtain ⟨h1, h2⟩ := h
    simp only [mapAh, List.map_cons, h1]
    rw [mapAh_eq_map g f rs (a + r.size) h2]

lemma serve_conserve (batch : Fin n → Bool) : ∀ (l : List (Req n)) (w : ℝ),
    ((serve batch l w).1.map Req.alloc).sum + (serve batch l w).2.1 = (l.map Req.alloc).sum + w
  | [], w => by simp [serve]
  | r :: rs, w => by
    rw [serve_cons']
    simp only [List.map_cons, List.sum_cons]
    have := serve_conserve batch rs (w - min (r.size - r.alloc) w)
    linarith

/-- Service of one request: allocation, shipment and whether it stays in the queue. -/
lemma serveElem_props (batch : Fin n → Bool) (L a : ℝ) (r : Req n) (h0 : 0 < r.size)
    (h1 : r.alloc < r.size) (h2 : 0 ≤ r.shipped) (h3 : r.shipped ≤ r.alloc)
    (h4 : r.alloc ≤ max 0 (min r.size (L - a))) :
    (serveElem batch L r a).alloc = max 0 (min r.size (L - a)) ∧
    0 ≤ (serveElem batch L r a).shipped ∧
    (serveElem batch L r a).shipped ≤ (serveElem batch L r a).alloc ∧
    ((serveElem batch L r a).shipped < r.size ↔ L - a < r.size) ∧
    (¬ L - a < r.size → (serveElem batch L r a).shipped = r.size ∧
      (serveElem batch L r a).alloc = r.size) := by
  have hA : (serveElem batch L r a).alloc = max 0 (min r.size (L - a)) := rfl
  have hS : (serveElem batch L r a).shipped = if batch r.ret = false ∨
      crossesThreshold r.size r.offset r.alloc (max 0 (min r.size (L - a)))
      then max 0 (min r.size (L - a)) else r.shipped := rfl
  have hA0 : 0 ≤ max 0 (min r.size (L - a)) := le_max_left _ _
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · rw [hS]; split_ifs <;> linarith
  · rw [hS, hA]; split_ifs <;> linarith
  · rw [hS]
    constructor
    · intro hlt
      by_contra hge
      rw [not_lt] at hge
      have : max 0 (min r.size (L - a)) = r.size :=
        by rw [min_eq_left hge, max_eq_right h0.le]
      split_ifs at hlt with hc
      · linarith
      · exact hc (Or.inr (Or.inr (Or.inr ⟨h1, this⟩)))
    · intro hlt
      have hlt' : max 0 (min r.size (L - a)) < r.size := by
        rcases le_total (L - a) 0 with h | h
        · rw [min_eq_right (by linarith), max_eq_left h]; exact h0
        · rw [min_eq_right hlt.le, max_eq_right h]; exact hlt
      split_ifs <;> linarith
  · intro hge
    rw [not_lt] at hge
    have : max 0 (min r.size (L - a)) = r.size := by rw [min_eq_left hge, max_eq_right h0.le]
    refine ⟨?_, by rw [hA, this]⟩
    rw [hS, if_pos (Or.inr (Or.inr (Or.inr ⟨h1, this⟩))), this]

lemma sum_filter_of_zero {β : Type} (l : List β) (p : β → Bool) (f : β → ℝ)
    (h : ∀ x ∈ l, p x = false → f x = 0) : ((l.filter p).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases hp : p a = true
    · simp [List.filter_cons_of_pos hp, ih']
    · rw [List.filter_cons_of_neg hp, ih', List.map_cons, List.sum_cons,
        h a List.mem_cons_self (by simpa using hp), zero_add]

lemma pi_sum_apply (l : List (Req n)) (f : Req n → ℝ) (i : Fin n) :
    ((l.map (fun r => (Pi.single r.ret (f r) : Fin n → ℝ))).sum) i
      = ((l.filter (fun r => r.ret = i)).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, ih]
    by_cases h : a.ret = i
    · subst h; simp
    · rw [Pi.single_apply, if_neg (Ne.symm h), zero_add, List.filter_cons_of_neg (by simpa using h)]


/-! ### Explicit data along a running period -/

section step

variable (N : Network n) (c : ConChoice n) (act : (ℕ → DemandVec n) → ℕ → Prop)
  [∀ d, DecidablePred (act d)] (Yp : (ℕ → DemandVec n) → ℕ → ℝ)
  (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ) (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)

lemma q0x_nonneg (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (t : ℕ) : 0 ≤ q0x c act Yp d t := by
  unfold q0x
  split_ifs with h
  · linarith [h.2]
  · exact le_rfl

lemma Vx_nonneg (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (t : ℕ) : 0 ≤ Vx N c act Yp d t :=
  Finset.sum_nonneg fun r _ => q0x_nonneg c act Yp hs0S d r

lemma Vx_mono (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) {t t' : ℕ} (h : t ≤ t') :
    Vx N c act Yp d t ≤ Vx N c act Yp d t' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    fun r _ _ => q0x_nonneg c act Yp hs0S d r

lemma Vx_succ (d : ℕ → DemandVec n) (t : ℕ) (ht : N.L0 ≤ t) :
    Vx N c act Yp d (t + 1) = Vx N c act Yp d t + q0x c act Yp d (t + 1 - N.L0) := by
  unfold Vx
  rw [show t + 1 + 1 - N.L0 = (t + 1 - N.L0) + 1 by omega, Finset.sum_range_succ]

variable (hq0 : ∀ d s i, 0 ≤ q d s i) (hs0S : c.s0 ≤ c.S0)
include hq0 hs0S

/-- The pending predicate is upward closed along the creation order. -/
lemma Lpre_eq_dropWhile (d : ℕ → DemandVec n) (t : ℕ) :
    Lpre N c act Yp q d t = (Lall (q d) t).dropWhile (fun k => !decide (k.1 = t ∨
      Vx N c act Yp d (t - 1) < ahx (q d) k.1 k.2 + q d k.1 k.2)) := by
  unfold Lpre
  apply filter_eq_dropWhile
  have h1 := Lall_pairwise (q d) (hq0 d) t
  have h2 := Lall_pairwise_born (q d) (hq0 d) t
  refine (h1.and h2).imp_of_mem fun {k k'} hk hk' h => ?_
  rw [mem_Lall] at hk hk'
  simp only [decide_eq_true_eq]
  rintro (h3 | h3)
  · left; omega
  · right; linarith [h.1, hk'.2]

lemma Lpre_run (d : ℕ → DemandVec n) (t : ℕ) (ht : 1 ≤ t) :
    ∃ a0, RunAh (fun k => ahx (q d) k.1 k.2) (fun k => q d k.1 k.2) (Lpre N c act Yp q d t) a0 ∧
      a0 ≤ min (Vx N c act Yp d (t - 1)) (Pq (q d) t) ∧
      a0 + ((Lpre N c act Yp q d t).map (fun k => q d k.1 k.2)).sum = Pq (q d) (t + 1) := by
  set p : ℕ × Fin n → Bool := fun k => !decide (k.1 = t ∨
      Vx N c act Yp d (t - 1) < ahx (q d) k.1 k.2 + q d k.1 k.2) with hp
  have hdrop := Lpre_eq_dropWhile N c act Yp q hq0 hs0S d t
  refine ⟨0 + (((Lall (q d) t).takeWhile p).map (fun k => q d k.1 k.2)).sum, ?_, ?_, ?_⟩
  · rw [hdrop]
    exact RunAh_dropWhile _ _ p _ 0 (RunAh_Lall (q d) (hq0 d) t)
  · refine RunAh_takeWhile_le _ _ p _ _ 0 (RunAh_Lall (q d) (hq0 d) t)
      (le_min (Vx_nonneg N c act Yp hs0S d _) (Finset.sum_nonneg fun r _ =>
        Finset.sum_nonneg fun j _ => hq0 d r j)) fun k hk hpk => ?_
    rw [mem_Lall] at hk
    simp only [hp, Bool.not_eq_true', decide_eq_false_iff_not, not_or, not_lt] at hpk
    refine le_min hpk.2 ?_
    exact (ahx_add_le (q d) (hq0 d) k.1 k.2).trans (Pq_mono (q d) (hq0 d) (by omega))
  · rw [zero_add, hdrop, ← List.sum_append, ← List.map_append, List.takeWhile_append_dropWhile,
      sum_Lall (q d) (hq0 d)]

/-- Allocation in a running period: the cumulative level rises to `V_t`. -/
lemma serve_step (d : ℕ → DemandVec n) (t : ℕ) (ht : 1 ≤ t) (Z : EngState n)
    (hI : InvP N c act Yp Ph q d t Z) (batch : Fin n → Bool) :
    (serve batch Z.queue Z.Wbar).1 = Z.queue.map (fun r =>
      serveElem batch (Vx N c act Yp d t) r (ahx (q d) r.born r.ret)) ∧
    (serve batch Z.queue Z.Wbar).2.1 = max 0 (Vx N c act Yp d t - Pq (q d) (t + 1)) ∧
    (serve batch Z.queue Z.Wbar).2.2 = (Z.queue.map (fun r => (Pi.single r.ret
      ((serveElem batch (Vx N c act Yp d t) r (ahx (q d) r.born r.ret)).shipped - r.shipped)
        : Fin n → ℝ))).sum := by
  obtain ⟨a0, hrun, ha0, hsum⟩ := Lpre_run N c act Yp q hq0 hs0S d t ht
  rw [← hI.keys] at hrun hsum
  rw [RunAh_map] at hrun
  have hrun' : RunAh (fun r => ahx (q d) r.born r.ret) Req.size Z.queue a0 :=
    (RunAh_congr _ _ _ _ (fun r _ => rfl) (fun r hr => (hI.elems r hr).1.symm)).1 hrun
  have hsz : (Z.queue.map Req.size).sum = ((Z.queue.map key).map (fun k => q d k.1 k.2)).sum := by
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun r hr => (hI.elems r hr).1
  set U := min (Vx N c act Yp d (t - 1)) (Pq (q d) t) with hU
  have hcont : ContigA Z.queue a0 U :=
    ContigA_of_RunAh _ U Z.queue a0 hrun' fun r hr => by
      refine ⟨by rw [(hI.elems r hr).1]; exact hq0 d _ _, (hI.elems r hr).2.1⟩
  have hUle : U ≤ a0 + (Z.queue.map Req.size).sum := by
    rw [hsz, hsum, hU]
    exact (min_le_right _ _).trans (Pq_mono (q d) (hq0 d) (by omega))
  have hw : 0 ≤ Z.Wbar := by
    rw [hI.wbar]
    have := Vx_mono N c act Yp hs0S d (show t - 1 ≤ t by omega)
    have := le_max_right (Vx N c act Yp d (t - 1) - Pq (q d) t) 0
    linarith
  have hUw : U + Z.Wbar = Vx N c act Yp d t := by
    rw [hI.wbar, hU]
    rcases le_total (Vx N c act Yp d (t - 1)) (Pq (q d) t) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  obtain ⟨h1, h2, h3⟩ := serve_contig batch Z.queue a0 U Z.Wbar ha0 hUle hw hcont
  rw [hUw] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, mapAh_eq_map _ _ _ _ hrun']
  · rw [h2, hsz, hsum]
  · rw [h3, mapAh_eq_map _ _ _ _ hrun']

/-- Elementary bounds for the requests of the queue. -/
lemma elem_facts (d : ℕ → DemandVec n) (t : ℕ) (ht : 1 ≤ t) (Z : EngState n)
    (hI : InvP N c act Yp Ph q d t Z) (r : Req n) (hr : r ∈ Z.queue) :
    0 < r.size ∧ r.alloc < r.size ∧ 0 ≤ r.shipped ∧ r.shipped ≤ r.alloc ∧
      r.alloc ≤ max 0 (min r.size (Vx N c act Yp d t - ahx (q d) r.born r.ret)) := by
  obtain ⟨hs, ha, hsh0, hsh⟩ := hI.elems r hr
  have hk : key r ∈ Lpre N c act Yp q d t := by
    rw [← hI.keys]; exact List.mem_map_of_mem hr
  unfold Lpre at hk
  rw [List.mem_filter, mem_Lall] at hk
  obtain ⟨⟨hkt, hkq⟩, hkp0⟩ := hk
  have hkp : r.born = t ∨ Vx N c act Yp d (t - 1) < ahx (q d) r.born r.ret + q d r.born r.ret :=
    of_decide_eq_true hkp0
  simp only [key] at hkt hkq
  have hpos : 0 < r.size := by rw [hs]; exact hkq
  have hVm := Vx_mono N c act Yp hs0S d (show t - 1 ≤ t by omega)
  refine ⟨hpos, ?_, hsh0, hsh, ?_⟩
  · rw [ha]
    rcases hkp with h | h
    · have h1 := ahx_nonneg (q d) (hq0 d) r.born r.ret
      rw [h] at h1
      have : min (Vx N c act Yp d (t - 1)) (Pq (q d) t) - ahx (q d) r.born r.ret ≤ 0 := by
        rw [h]; linarith [min_le_right (Vx N c act Yp d (t - 1)) (Pq (q d) t)]
      rw [max_eq_left (min_le_of_right_le this)]; exact hpos
    · have : min (Vx N c act Yp d (t - 1)) (Pq (q d) t) - ahx (q d) r.born r.ret < r.size := by
        rw [hs]; linarith [min_le_left (Vx N c act Yp d (t - 1)) (Pq (q d) t)]
      rcases le_total (min (Vx N c act Yp d (t - 1)) (Pq (q d) t) - ahx (q d) r.born r.ret) 0
        with h' | h'
      · rw [max_eq_left (min_le_of_right_le h')]; exact hpos
      · rw [min_eq_right this.le, max_eq_right h']; exact this
  · rw [ha]
    refine max_le_max le_rfl (min_le_min le_rfl ?_)
    linarith [min_le_left (Vx N c act Yp d (t - 1)) (Pq (q d) t)]

/-- Step 3 of a running period (allocation and dispatch). -/
lemma phaseB_step (d : ℕ → DemandVec n) (t : ℕ) (ht : 1 ≤ t) (Z : EngState n)
    (hI : InvP N c act Yp Ph q d t Z) (Pb : EngParams n) :
    let F := fun r : Req n => serveElem Pb.batch (Vx N c act Yp d t) r (ahx (q d) r.born r.ret)
    (phaseB N.L Pb t Z).1.Wbar = max 0 (Vx N c act Yp d t - Pq (q d) (t + 1)) ∧
    (phaseB N.L Pb t Z).1.queue = (Z.queue.map F).filter (fun r => decide (r.shipped < r.size)) ∧
    (phaseB N.L Pb t Z).1.supPipe = Z.supPipe ∧
    (phaseB N.L Pb t Z).1.nOrd = Z.nOrd ∧
    (∀ i r, t + N.L i < r → (phaseB N.L Pb t Z).1.retPipe i r = 0) ∧
    (phaseB N.L Pb t Z).2 = (Z.queue.map (fun r => (Pi.single r.ret
      ((F r).shipped - r.shipped) : Fin n → ℝ))).sum ∧
    posE N.L0 N.L c.S (phaseB N.L Pb t Z).1 t = posE N.L0 N.L c.S Z t ∧
    ∀ i, phat N.L (phaseB N.L Pb t Z).1 t i = phat N.L Z t i := by
  intro F
  obtain ⟨h1, h2, h3⟩ := serve_step N c act Yp Ph q hq0 hs0S d t ht Z hI Pb.batch
  have hB : (phaseB N.L Pb t Z).1 = sendOut N.L t (serve Pb.batch Z.queue Z.Wbar).2.2
      { Z with
        Wbar := (serve Pb.batch Z.queue Z.Wbar).2.1
        queue := List.filter (fun r => decide (r.shipped < r.size)) (serve Pb.batch Z.queue Z.Wbar).1 } :=
    rfl
  have hB2 : (phaseB N.L Pb t Z).2 = (serve Pb.batch Z.queue Z.Wbar).2.2 := rfl
  -- requests leaving the queue are fully shipped
  have hgone : ∀ x ∈ Z.queue.map F, decide (x.shipped < x.size) = false →
      x.alloc - x.shipped = 0 ∧ x.size - x.shipped = 0 := by
    intro x hx hxs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    obtain ⟨e1, e2, e3, e4, e5⟩ := elem_facts N c act Yp Ph q hq0 hs0S d t ht Z hI r hr
    obtain ⟨p1, p2, p3, p4, p5⟩ := serveElem_props Pb.batch (Vx N c act Yp d t)
      (ahx (q d) r.born r.ret) r e1 e2 e3 e4 e5
    simp only [decide_eq_false_iff_not] at hxs
    have := p5 (fun h => hxs (p4.2 h))
    have hsz : (F r).size = r.size := rfl
    constructor
    · show (F r).alloc - (F r).shipped = 0
      rw [this.1, this.2, sub_self]
    · show (F r).size - (F r).shipped = 0
      rw [hsz, this.1, sub_self]
  have hship : ∀ i, (serve Pb.batch Z.queue Z.Wbar).2.2 i
      = qterm Z.queue i (fun r => (F r).shipped - r.shipped) := fun i => by
    rw [h3, pi_sum_apply]; rfl
  have hretF : ∀ i, ((Z.queue.map F).filter (fun r => r.ret = i))
      = (Z.queue.filter (fun r => r.ret = i)).map F := fun i => by
    rw [List.filter_map]; rfl
  refine ⟨by rw [hB]; exact h2, by rw [hB]; simp only [sendOut_queue]; rw [h1], by rw [hB]; rfl,
    by rw [hB]; rfl, ?_, by rw [hB2, h3], ?_, ?_⟩
  · intro i r hr
    rw [hB, sendOut_retPipe_far _ _ _ _ i r hr]
    exact hI.ret i r hr
  · -- the supplier position is unchanged
    unfold posE
    rw [hB]
    simp only [sendOut_Wbar, physPos_sendOut]
    have hres : ∑ i, reserve (sendOut N.L t (serve Pb.batch Z.queue Z.Wbar).2.2
        { Z with
          Wbar := (serve Pb.batch Z.queue Z.Wbar).2.1
          queue := List.filter (fun r => decide (r.shipped < r.size))
            (serve Pb.batch Z.queue Z.Wbar).1 }) i
        = ((Z.queue.map F).map (fun r => r.alloc - r.shipped)).sum := by
      rw [sum_reserve]
      simp only [sendOut_queue]
      rw [h1]
      exact sum_filter_of_zero _ _ _ fun x hx hxs => (hgone x hx hxs).1
    have hsup : supInTransit N.L0 (sendOut N.L t (serve Pb.batch Z.queue Z.Wbar).2.2
        { Z with
          Wbar := (serve Pb.batch Z.queue Z.Wbar).2.1
          queue := List.filter (fun r => decide (r.shipped < r.size))
            (serve Pb.batch Z.queue Z.Wbar).1 }) t = supInTransit N.L0 Z t := rfl
    have hphys : ∀ i, physPos N.L { Z with
          Wbar := (serve Pb.batch Z.queue Z.Wbar).2.1
          queue := List.filter (fun r => decide (r.shipped < r.size))
            (serve Pb.batch Z.queue Z.Wbar).1 } t i = physPos N.L Z t i := fun i => rfl
    have hc1 : (Z.queue.map (fun r => (F r).alloc)).sum + (serve Pb.batch Z.queue Z.Wbar).2.1
        = (Z.queue.map Req.alloc).sum + Z.Wbar := by
      have := serve_conserve Pb.batch Z.queue Z.Wbar
      rw [h1, List.map_map] at this
      exact this
    have hc2 : ((Z.queue.map F).map (fun r => r.alloc - r.shipped)).sum
        = (Z.queue.map (fun r => (F r).alloc)).sum - (Z.queue.map (fun r => (F r).shipped)).sum := by
      rw [List.map_map, ← sum_map_sub_list]; rfl
    have hc3 : (Z.queue.map (fun r => (F r).shipped - r.shipped)).sum
        = (Z.queue.map (fun r => (F r).shipped)).sum - (Z.queue.map Req.shipped).sum :=
      sum_map_sub_list _ _ _
    have hc4 : (Z.queue.map (fun r => r.alloc - r.shipped)).sum
        = (Z.queue.map Req.alloc).sum - (Z.queue.map Req.shipped).sum := sum_map_sub_list _ _ _
    have e1 : ∑ i, (physPos N.L Z t i + qterm Z.queue i (fun r => (F r).shipped - r.shipped)
        - c.S i) = ∑ i, (physPos N.L Z t i - c.S i)
          + (Z.queue.map (fun r => (F r).shipped - r.shipped)).sum := by
      rw [← sum_qterm, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hres, hsup]
    simp only [hphys, hship]
    rw [e1, sum_reserve, hc2, hc3, hc4]
    linarith
  · intro i
    rw [phat_eq, phat_eq, hB]
    simp only [physPos_sendOut, sendOut_queue]
    have hphys : physPos N.L { Z with
          Wbar := (serve Pb.batch Z.queue Z.Wbar).2.1
          queue := List.filter (fun r => decide (r.shipped < r.size))
            (serve Pb.batch Z.queue Z.Wbar).1 } t i = physPos N.L Z t i := rfl
    rw [hphys, hship, h1]
    have hq2 : qterm (List.filter (fun r => decide (r.shipped < r.size)) (Z.queue.map F)) i
        (fun r => r.size - r.shipped) = qterm Z.queue i (fun r => r.size - (F r).shipped) := by
      unfold qterm
      rw [List.filter_comm,
        sum_filter_of_zero (List.filter (fun r => decide (r.ret = i)) (List.map F Z.queue))
          (fun r => decide (r.shipped < r.size)) (fun r => r.size - r.shipped) ?_, hretF,
        List.map_map]
      · rfl
      · intro x hx hxs
        rw [List.mem_filter] at hx
        exact (hgone x hx.1 hxs).2
    rw [hq2, add_assoc]
    congr 1
    unfold qterm
    rw [← sum_map_add_list]
    congr 1
    apply List.map_congr_left
    intro r _
    ring

/-- Requests kept in the queue after the allocation of period `t`. -/
lemma phaseB_keys (d : ℕ → DemandVec n) (t : ℕ) (ht : 1 ≤ t) (Z : EngState n)
    (hI : InvP N c act Yp Ph q d t Z) (Pb : EngParams n) :
    (phaseB N.L Pb t Z).1.queue.map key = (Lall (q d) t).filter (fun k =>
      decide (Vx N c act Yp d t < ahx (q d) k.1 k.2 + q d k.1 k.2)) := by
  obtain ⟨-, b2, -⟩ := phaseB_step N c act Yp Ph q hq0 hs0S d t ht Z hI Pb
  set F := fun r : Req n => serveElem Pb.batch (Vx N c act Yp d t) r (ahx (q d) r.born r.ret)
    with hF
  have hVm := Vx_mono N c act Yp hs0S d (show t - 1 ≤ t by omega)
  rw [b2, List.filter_map, List.map_map]
  have hkF : key ∘ F = key := rfl
  rw [hkF]
  have : Z.queue.filter ((fun r => decide (r.shipped < r.size)) ∘ F)
      = Z.queue.filter ((fun k => decide (Vx N c act Yp d t < ahx (q d) k.1 k.2 + q d k.1 k.2))
        ∘ key) := by
    apply List.filter_congr
    intro r hr
    obtain ⟨e1, e2, e3, e4, e5⟩ := elem_facts N c act Yp Ph q hq0 hs0S d t ht Z hI r hr
    obtain ⟨p1, p2, p3, p4, p5⟩ := serveElem_props Pb.batch (Vx N c act Yp d t)
      (ahx (q d) r.born r.ret) r e1 e2 e3 e4 e5
    have hsz := (hI.elems r hr).1
    have hiff : (F r).shipped < (F r).size ↔
        Vx N c act Yp d t < ahx (q d) (key r).1 (key r).2 + q d (key r).1 (key r).2 := by
      show (F r).shipped < r.size ↔
        Vx N c act Yp d t < ahx (q d) r.born r.ret + q d r.born r.ret
      rw [← hsz]
      exact p4.trans (by constructor <;> intro h <;> linarith)
    exact decide_eq_decide.mpr hiff
  rw [this, ← List.filter_map, hI.keys]
  unfold Lpre
  rw [List.filter_filter]
  apply List.filter_congr
  intro k hk
  by_cases h2 : Vx N c act Yp d t < ahx (q d) k.1 k.2 + q d k.1 k.2
  · have h1 : k.1 = t ∨ Vx N c act Yp d (t - 1) < ahx (q d) k.1 k.2 + q d k.1 k.2 :=
      Or.inr (by linarith)
    simp [h1, h2]
  · simp [h2]

end step

/-! ### Step 2 of a period: requests and the supplier order -/

section phaseA

lemma sum_map_ite_eq_nodup {β : Type} [DecidableEq β] (f : β → ℝ) (i : β) :
    ∀ (l : List β), l.Nodup → (l.map (fun j => if j = i then f j else 0)).sum
      = if i ∈ l then f i else 0
  | [], _ => by simp
  | a :: l, h => by
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.sum_cons, List.mem_cons]
    rw [sum_map_ite_eq_nodup f i l h.2]
    by_cases ha : a = i
    · subst ha; simp [h.1]
    · simp only [ha, if_false, zero_add]
      by_cases hi : i ∈ l
      · simp [hi]
      · simp [hi, Ne.symm ha]

lemma qterm_eq_map (l : List (Req n)) (i : Fin n) (f : Req n → ℝ) :
    qterm l i f = (l.map (fun r => if r.ret = i then f r else 0)).sum := by
  unfold qterm
  rw [sum_map_filter_ite']
  simp only [decide_eq_true_eq]

lemma qterm_append (l1 l2 : List (Req n)) (i : Fin n) (f : Req n → ℝ) :
    qterm (l1 ++ l2) i f = qterm l1 i f + qterm l2 i f := by
  unfold qterm
  rw [List.filter_append, List.map_append, List.sum_append]

variable (L0 : ℕ) (L : Fin n → ℕ) (P : EngParams n) (rule : OffsetRule n) (t : ℕ) (st : EngState n)

/-- The new requests of step 2. -/
def newRA : List (Req n) :=
  ((List.finRange n).filter (fun i => decide (0 < reqSize L P st t i))).mapIdx (fun k i =>
    ({ ret := i, size := reqSize L P st t i, alloc := 0, shipped := 0,
       offset := if P.batch i then rule
          { st with
            Wbar := if L0 = 0 then st.Wbar + (phaseA L0 L P rule t st).2 else st.Wbar
            supPipe := if L0 = 0 then st.supPipe
              else Function.update st.supPipe (t + L0)
                (st.supPipe (t + L0) + (phaseA L0 L P rule t st).2)
            queue := st.queue ++ ((List.finRange n).filter
              (fun i => decide (0 < reqSize L P st t i))).map (fun i =>
                ({ ret := i, size := reqSize L P st t i, alloc := 0, shipped := 0, offset := 0,
                   born := t } : Req n))
            nOrd := st.nOrd + ((List.finRange n).filter
              (fun i => decide (0 < reqSize L P st t i))).length }
          t (st.nOrd + k + 1) i (reqSize L P st t i) else 0,
       born := t } : Req n))

lemma phaseA_snd :
    (phaseA L0 L P rule t st).2 = if posE L0 L P.center st t ≤ P.s0 then
      P.S0 - posE L0 L P.center st t else 0 := rfl

lemma phaseA_fst :
    (phaseA L0 L P rule t st).1 =
      { st with
        Wbar := if L0 = 0 then st.Wbar + (phaseA L0 L P rule t st).2 else st.Wbar
        supPipe := if L0 = 0 then st.supPipe
          else Function.update st.supPipe (t + L0) (st.supPipe (t + L0) + (phaseA L0 L P rule t st).2)
        queue := st.queue ++ newRA L0 L P rule t st
        nOrd := st.nOrd + ((List.finRange n).filter (fun i => decide (0 < reqSize L P st t i))).length } :=
  rfl

lemma newRA_keys : (newRA L0 L P rule t st).map key
    = ((List.finRange n).filter (fun i => decide (0 < reqSize L P st t i))).map (fun i => (t, i)) :=
  map_mapIdx_const _ _ _ _ fun _ _ => rfl

lemma newRA_mem : ∀ r ∈ newRA L0 L P rule t st, r.size = reqSize L P st t r.ret ∧ r.alloc = 0 ∧
    r.shipped = 0 ∧ r.born = t :=
  mem_mapIdx_prop _ _ _ fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

lemma qterm_newRA (i : Fin n) :
    qterm (newRA L0 L P rule t st) i (fun r => r.size - r.shipped)
      = if 0 < reqSize L P st t i then reqSize L P st t i else 0 := by
  rw [qterm_eq_map]
  unfold newRA
  rw [map_mapIdx_const _ (fun j => if j = i then reqSize L P st t j else 0) _ _ (fun k j => by
    simp only [sub_zero])]
  rw [sum_map_ite_eq_nodup _ _ _ ((List.nodup_finRange n).filter _)]
  simp [List.mem_filter]

lemma posE_phaseA :
    posE L0 L P.center (phaseA L0 L P rule t st).1 t
      = posE L0 L P.center st t + (phaseA L0 L P rule t st).2 := by
  have hres : ∑ i, reserve (phaseA L0 L P rule t st).1 i = ∑ i, reserve st i := by
    rw [sum_reserve, sum_reserve, phaseA_fst]
    simp only [List.map_append, List.sum_append]
    have : ((newRA L0 L P rule t st).map (fun r => r.alloc - r.shipped)).sum = 0 :=
      List.sum_eq_zero fun x hx => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
        rw [(newRA_mem L0 L P rule t st r hr).2.1, (newRA_mem L0 L P rule t st r hr).2.2.1, sub_self]
    rw [this, add_zero]
  have hphys : ∀ i, physPos L (phaseA L0 L P rule t st).1 t i = physPos L st t i := fun i => rfl
  unfold posE
  rw [hres]
  simp only [hphys]
  rw [phaseA_fst]
  unfold supInTransit
  dsimp only
  by_cases h0 : L0 = 0
  · simp only [h0, if_true, Finset.range_zero, Finset.sum_empty]
    ring
  · simp only [h0, if_false]
    have hmem : L0 - 1 ∈ Finset.range L0 := Finset.mem_range.2 (by omega)
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
    have e1 : t + 1 + (L0 - 1) = t + L0 := by omega
    rw [e1, Function.update_self]
    have e2 : ∑ x ∈ (Finset.range L0).erase (L0 - 1), Function.update st.supPipe (t + L0)
        (st.supPipe (t + L0) + (phaseA L0 L P rule t st).2) (t + 1 + x)
        = ∑ x ∈ (Finset.range L0).erase (L0 - 1), st.supPipe (t + 1 + x) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Function.update_of_ne]
      have := Finset.ne_of_mem_erase hk
      omega
    rw [e2]
    ring

lemma phat_phaseA (i : Fin n) :
    phat L (phaseA L0 L P rule t st).1 t i
      = phat L st t i + (if 0 < reqSize L P st t i then reqSize L P st t i else 0) := by
  rw [phat_eq, phat_eq]
  have hphys : physPos L (phaseA L0 L P rule t st).1 t i = physPos L st t i := rfl
  rw [hphys, phaseA_fst]
  dsimp only
  rw [qterm_append, qterm_newRA]
  ring

end phaseA

/-! ### The generic period step -/

section gstep

variable (N : Network n) (c : ConChoice n) (act : (ℕ → DemandVec n) → ℕ → Prop)
  [∀ d, DecidablePred (act d)] (Yp : (ℕ → DemandVec n) → ℕ → ℝ)
  (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ) (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hq0 : ∀ d s i, 0 ≤ q d s i) (hs0S : c.s0 ≤ c.S0)
  (hY : ∀ d t, Yp d (t + 1) = (if act d t ∧ Yp d t ≤ c.s0 then c.S0 else Yp d t)
    - ∑ i, ((d t i : ℝ≥0) : ℝ))
  (hPh : ∀ d t i, Ph d (t + 1) i = if act d t then
    (if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i else Ph d t i - ((d t i : ℝ≥0) : ℝ))
    else c.S i)
  (hqo : ∀ d t i, act d t → q d (t + 1) i = if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then
    c.S i - (Ph d t i - ((d t i : ℝ≥0) : ℝ)) else 0)
  (hmono : ∀ d t, act d t → act d (t + 1))
  (hL0 : ∀ d t, act d t → N.L0 ≤ t)
include hq0 hs0S hY hPh hqo hmono hL0

theorem step_generic (d : ℕ → DemandVec n) (t : ℕ) (ht : 1 ≤ t) (hact : act d t) (Z : EngState n)
    (hI : InvP N c act Yp Ph q d t Z) (P Pb : EngParams n)
    (hP : P.s = c.s ∧ P.S = c.S ∧ P.center = c.S ∧ P.s0 = c.s0 ∧ P.S0 = c.S0)
    (rule : OffsetRule n) :
    InvP N c act Yp Ph q d (t + 1) (phaseA N.L0 N.L P rule (t + 1)
      (receive (applyDemand (phaseB N.L Pb t Z).1 (d t)) (t + 1))).1 ∧
    (phaseA N.L0 N.L P rule (t + 1)
      (receive (applyDemand (phaseB N.L Pb t Z).1 (d t)) (t + 1))).2 = q0x c act Yp d (t + 1) := by
  obtain ⟨hPs, hPS, hPc, hPs0, hPS0⟩ := hP
  obtain ⟨b1, b2, b3, b4, b5, -, b7, b8⟩ := phaseB_step N c act Yp Ph q hq0 hs0S d t ht Z hI Pb
  set F := fun r : Req n => serveElem Pb.batch (Vx N c act Yp d t) r (ahx (q d) r.born r.ret)
    with hF
  set B := (phaseB N.L Pb t Z).1 with hB
  set R := receive (applyDemand B (d t)) (t + 1) with hR
  have hact1 := hmono d t hact
  have hLt := hL0 d t hact
  -- the state after the receipts of period `t + 1`
  have hsup0 : B.supPipe (t + 1 + N.L0) = 0 := by
    rw [b3, hI.sup _ (by omega)]
    rw [if_neg (by omega)]
  have hret0 : ∀ i, (applyDemand B (d t)).retPipe i (t + 1 + N.L i) = 0 := fun i =>
    b5 i _ (by omega)
  have hYs : Yp d (t + 1) = Ypost c Yp d t - ∑ i, ((d t i : ℝ≥0) : ℝ) := by
    rw [hY]; simp only [hact, true_and]; rfl
  have hposR : posE N.L0 N.L c.S R (t + 1) = Yp d (t + 1) := by
    rw [hR, posE_receive _ _ _ _ _ (by simpa using hsup0) hret0, posE_applyDemand, b7, hI.pos, hYs]
  have hphatR : ∀ i, phat N.L R (t + 1) i = Ph d t i - ((d t i : ℝ≥0) : ℝ) := fun i => by
    rw [hR, phat_receive _ _ _ _ (hret0 i), phat_applyDemand, b8, hI.phat]
  have hreq : ∀ i, reqSize N.L P R (t + 1) i = q d (t + 1) i := fun i => by
    unfold reqSize
    rw [hphatR, hPs, hPS, hqo d t i hact]
  have hq0' : (phaseA N.L0 N.L P rule (t + 1) R).2 = q0x c act Yp d (t + 1) := by
    rw [phaseA_snd, hPc, hPs0, hPS0, hposR]
    unfold q0x
    simp only [hact1, true_and]
  have hrs : ((List.finRange n).filter (fun i => decide (0 < reqSize N.L P R (t + 1) i)))
      = (List.finRange n).filter (fun i => decide (0 < q d (t + 1) i)) :=
    List.filter_congr fun i _ => by rw [hreq]
  have hRW : R.Wbar = max 0 (Vx N c act Yp d t - Pq (q d) (t + 1)) + Z.supPipe (t + 1) := by
    rw [hR]; simp only [receive_Wbar, applyDemand_Wbar, applyDemand_supPipe]; rw [b1, b3]
  have hZsup1 : Z.supPipe (t + 1) = if 0 < N.L0 then q0x c act Yp d (t + 1 - N.L0) else 0 := by
    rw [hI.sup _ (by omega)]
    by_cases h0 : 0 < N.L0
    · rw [if_pos ⟨h0, by omega⟩, if_pos h0]
    · rw [if_neg (fun h => h0 h.1), if_neg h0]
  have hV1 := Vx_succ N c act Yp d t hLt
  have hVm := Vx_mono N c act Yp hs0S d (show t - 1 ≤ t by omega)
  have ht1 : t + 1 - 1 = t := by omega
  set Z' := (phaseA N.L0 N.L P rule (t + 1) R).1 with hZ'
  have hZW : Z'.Wbar = if N.L0 = 0 then R.Wbar + q0x c act Yp d (t + 1) else R.Wbar := by
    rw [hZ', phaseA_fst, hq0']
  have hZsup : Z'.supPipe = if N.L0 = 0 then R.supPipe else Function.update R.supPipe
      (t + 1 + N.L0) (R.supPipe (t + 1 + N.L0) + q0x c act Yp d (t + 1)) := by
    rw [hZ', phaseA_fst, hq0']
  have hZq : Z'.queue = R.queue ++ newRA N.L0 N.L P rule (t + 1) R := by rw [hZ', phaseA_fst]
  have hZn : Z'.nOrd = R.nOrd + ((List.finRange n).filter
      (fun i => decide (0 < reqSize N.L P R (t + 1) i))).length := by rw [hZ', phaseA_fst]
  have hZr : Z'.retPipe = R.retPipe := by rw [hZ', phaseA_fst]
  have hRq : R.queue = B.queue := rfl
  have hRsup : R.supPipe = Z.supPipe := by rw [hR]; simp only [receive_supPipe, applyDemand_supPipe]; exact b3
  refine ⟨?_, hq0'⟩
  constructor
  · -- unallocated warehouse stock
    rw [hZW, hRW, hZsup1, ht1, hV1, max_comm]
    by_cases h0 : N.L0 = 0
    · simp only [h0, if_true, lt_irrefl, if_false, Nat.sub_zero]; ring
    · simp only [h0, if_false, show 0 < N.L0 by omega, if_true]; ring
  · -- scheduled supplier receipts
    intro r hr
    rw [hZsup]
    by_cases h0 : N.L0 = 0
    · simp only [h0, if_true, lt_irrefl, false_and, if_false]
      rw [hRsup, hI.sup r (by omega), if_neg (by omega)]
    · simp only [h0, if_false]
      by_cases hr' : r = t + 1 + N.L0
      · subst hr'
        rw [Function.update_self, if_pos ⟨by omega, le_rfl⟩, hRsup]
        have := hsup0
        rw [b3] at this
        rw [this, zero_add, show t + 1 + N.L0 - N.L0 = t + 1 by omega]
      · rw [Function.update_of_ne hr', hRsup, hI.sup r (by omega)]
        by_cases hr2 : r ≤ t + N.L0
        · rw [if_pos ⟨by omega, hr2⟩, if_pos ⟨by omega, by omega⟩]
        · rw [if_neg (fun h => hr2 h.2), if_neg (fun h => hr' (by omega))]
  · -- the queue keys
    rw [hZq, List.map_append, newRA_keys, hrs]
    have hBk : (R.queue).map key = (Lall (q d) t).filter (fun k =>
        decide (Vx N c act Yp d t < ahx (q d) k.1 k.2 + q d k.1 k.2)) := by
      rw [hRq, b2, List.filter_map, List.map_map]
      have hkF : key ∘ F = key := rfl
      rw [hkF]
      have : Z.queue.filter ((fun r => decide (r.shipped < r.size)) ∘ F)
          = Z.queue.filter ((fun k => decide (Vx N c act Yp d t < ahx (q d) k.1 k.2 + q d k.1 k.2))
            ∘ key) := by
        apply List.filter_congr
        intro r hr
        obtain ⟨e1, e2, e3, e4, e5⟩ := elem_facts N c act Yp Ph q hq0 hs0S d t ht Z hI r hr
        obtain ⟨p1, p2, p3, p4, p5⟩ := serveElem_props Pb.batch (Vx N c act Yp d t)
          (ahx (q d) r.born r.ret) r e1 e2 e3 e4 e5
        have hsz := (hI.elems r hr).1
        have hiff : (F r).shipped < (F r).size ↔
            Vx N c act Yp d t < ahx (q d) (key r).1 (key r).2 + q d (key r).1 (key r).2 := by
          show (F r).shipped < r.size ↔
            Vx N c act Yp d t < ahx (q d) r.born r.ret + q d r.born r.ret
          rw [← hsz]
          exact p4.trans (by constructor <;> intro h <;> linarith)
        exact decide_eq_decide.mpr hiff
      rw [this, ← List.filter_map, hI.keys]
      unfold Lpre
      rw [List.filter_filter]
      apply List.filter_congr
      intro k hk
      by_cases h2 : Vx N c act Yp d t < ahx (q d) k.1 k.2 + q d k.1 k.2
      · have h1 : k.1 = t ∨ Vx N c act Yp d (t - 1) < ahx (q d) k.1 k.2 + q d k.1 k.2 :=
          Or.inr (by linarith)
        simp [h1, h2]
      · simp [h2]
    rw [hBk]
    unfold Lpre
    rw [Lall_succ, List.filter_append, ht1]
    congr 1
    · apply List.filter_congr
      intro k hk
      rw [mem_Lall] at hk
      simp only [show k.1 ≠ t + 1 by omega, false_or]
    · unfold perL
      refine (List.filter_eq_self.2 fun k hk => ?_).symm
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hk
      simp
  · -- the requests
    intro r hr
    rw [ht1]
    rw [hZq] at hr
    rcases List.mem_append.1 hr with hr | hr
    · rw [hRq, b2, List.mem_filter, List.mem_map] at hr
      obtain ⟨⟨r0, hr0, rfl⟩, hkeep⟩ := hr
      obtain ⟨e1, e2, e3, e4, e5⟩ := elem_facts N c act Yp Ph q hq0 hs0S d t ht Z hI r0 hr0
      obtain ⟨p1, p2, p3, p4, p5⟩ := serveElem_props Pb.batch (Vx N c act Yp d t)
        (ahx (q d) r0.born r0.ret) r0 e1 e2 e3 e4 e5
      have hk := p4.1 (of_decide_eq_true hkeep)
      have hsz : r0.size = q d r0.born r0.ret := (hI.elems r0 hr0).1
      have hkey : key r0 ∈ Lall (q d) t := by
        have : key r0 ∈ Lpre N c act Yp q d t := by rw [← hI.keys]; exact List.mem_map_of_mem hr0
        exact (List.mem_filter.1 this).1
      rw [mem_Lall] at hkey
      have hle : ahx (q d) r0.born r0.ret + q d r0.born r0.ret ≤ Pq (q d) (t + 1) :=
        (ahx_add_le (q d) (hq0 d) r0.born r0.ret).trans
          (Pq_mono (q d) (hq0 d) (by simp only [key] at hkey; omega))
      have hVle : Vx N c act Yp d t ≤ Pq (q d) (t + 1) := by rw [← hsz] at hle; linarith
      refine ⟨hsz, ?_, p2, p3⟩
      rw [p1, min_eq_left hVle]
      rfl
    · obtain ⟨m1, m2, m3, m4⟩ := newRA_mem N.L0 N.L P rule (t + 1) R r hr
      refine ⟨by rw [m1, m4, hreq], ?_, by rw [m3], by rw [m3, m2]⟩
      rw [m2, m4]
      have h1 := ahx_nonneg (q d) (hq0 d) (t + 1) r.ret
      rw [max_eq_left (min_le_of_right_le (by
        linarith [min_le_right (Vx N c act Yp d t) (Pq (q d) (t + 1))]))]
  · -- positions including outstanding requests
    intro i
    rw [hZ', phat_phaseA, hphatR, hreq, hPh, if_pos hact, hqo d t i hact]
    by_cases h : Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i
    · rw [if_pos h, if_pos h]
      by_cases h' : 0 < c.S i - (Ph d t i - ((d t i : ℝ≥0) : ℝ))
      · rw [if_pos h']; ring
      · rw [if_neg h']
        have := hq0 d (t + 1) i
        rw [hqo d t i hact, if_pos h] at this
        linarith
    · rw [if_neg h, if_neg h, if_neg (lt_irrefl 0), add_zero]
  · -- no shipments beyond the lead time
    intro i r hr
    rw [hZr, hR]; simp only [receive_retPipe, applyDemand_retPipe]
    exact b5 i r (by omega)
  · -- ordinary request count
    rw [hZn, hR]; simp only [receive_nOrd, applyDemand_nOrd]
    rw [b4, hI.nord, hrs]
    unfold nOx
    rw [Finset.sum_range_succ _ (t + 1)]
    simp only [show 0 < t + 1 by omega, add_tsub_cancel_right, hact, and_self, if_true]
  · -- the supplier position after the order
    have := posE_phaseA N.L0 N.L P rule (t + 1) R
    rw [hPc] at this
    rw [hZ', this, hposR, hq0']
    unfold Ypost q0x
    simp only [hact1, true_and]
    split_ifs <;> ring

end gstep

end OWMR.Eng


/-! Engine lemmas, part 6: the preparation phase of `π_con`. -/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR


namespace OWMR.Eng

variable {n : ℕ}

lemma L_le_Tpipe (N : Network n) (i : Fin n) : N.L i ≤ N.Tpipe :=
  le_trans (Finset.le_sup (f := N.L) (Finset.mem_univ i)) (le_max_right _ _)

lemma L0_le_Tpipe (N : Network n) : N.L0 ≤ N.Tpipe := le_max_left _ _

section prep

variable (N : Network n) (x : InitState n) (c : ConChoice n)

/-- Warehouse stock sent to `sendTo` at the end of the pipelines. -/
def W0 : ℝ := x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s

/-- Retailer net inventory at the start of a preparation period `t`. -/
def prepI (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  x.I i + ∑ r ∈ Finset.range t, (if r < N.L i then x.retPipe i r else 0)
    + (if i = c.sendTo ∧ N.Tpipe - 1 + N.L i < t then W0 N x else 0)
    - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)

/-- Scheduled retailer receipts during preparation. -/
def prepRet (t : ℕ) (i : Fin n) (r : ℕ) : ℝ :=
  (if r < N.L i then x.retPipe i r else 0)
    + (if i = c.sendTo ∧ N.L i ≠ 0 ∧ N.Tpipe - 1 < t ∧ r = N.Tpipe - 1 + N.L i then W0 N x else 0)

/-- Warehouse stock at the start of a preparation period `t`. -/
def prepW (t : ℕ) : ℝ :=
  if t ≤ N.Tpipe - 1 then x.W + ∑ r ∈ Finset.range t, (if r < N.L0 then x.supPipe r else 0) else 0

/-- The state at the start of a preparation period. -/
def prepState (d : ℕ → DemandVec n) (t : ℕ) : EngState n where
  running := false
  Wbar := prepW N x t
  I := prepI N x c d t
  supPipe := fun r => if r < N.L0 then x.supPipe r else 0
  retPipe := prepRet N x c t
  queue := []
  nOrd := 0

/-- Inventory after all prescribed arrivals and the shipment to `sendTo`. -/
def IPx (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
    + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
    - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ)

lemma sum_ite_lt_eq (f : ℕ → ℝ) (L t : ℕ) (h : L ≤ t) :
    ∑ r ∈ Finset.range t, (if r < L then f r else 0) = ∑ r ∈ Finset.range L, f r := by
  rw [← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- After the receipts of a period `t` past all prescribed arrivals, inventories are `IPx`. -/
lemma receive_prep_I (d : ℕ → DemandVec n) (t : ℕ) (ht1 : N.Tpipe - 1 < t)
    (ht2 : N.Tpipe - 1 + N.L c.sendTo ≤ t) (i : Fin n) :
    (receive (prepState N x c d t) t).I i = IPx N x c d t i := by
  simp only [receive, prepState, prepI, prepRet, IPx]
  have hLi := L_le_Tpipe N i
  rw [sum_ite_lt_eq _ _ _ (by omega), if_neg (show ¬ t < N.L i by omega)]
  by_cases hi : i = c.sendTo
  · subst hi
    by_cases hL : N.L c.sendTo = 0
    · rw [if_pos ⟨rfl, by omega⟩, if_neg (fun h => h.2.1 hL), if_pos rfl]; unfold W0; ring
    · rcases lt_or_eq_of_le ht2 with h | h
      · rw [if_pos ⟨rfl, h⟩, if_neg (fun h' => by omega), if_pos rfl]; unfold W0; ring
      · rw [if_neg (fun h' => by omega), if_pos ⟨rfl, hL, ht1, h.symm⟩, if_pos rfl]; unfold W0; ring
  · rw [if_neg (fun h => hi h.1), if_neg (fun h => hi h.1), if_neg hi]; ring

lemma prepI_step_T (d : ℕ → DemandVec n) (t : ℕ) (hT : t = N.Tpipe - 1) (i : Fin n) :
    (if N.L i = 0 then prepI N x c d t i + prepRet N x c t i t + (if i = c.sendTo then W0 N x else 0)
      else prepI N x c d t i + prepRet N x c t i t) - ((d t i : ℝ≥0) : ℝ)
      = prepI N x c d (t + 1) i := by
  unfold prepI prepRet
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hB : (i = c.sendTo ∧ N.Tpipe - 1 + N.L i < t) ↔ False := ⟨fun h => by omega, False.elim⟩
  have hC : (i = c.sendTo ∧ N.L i ≠ 0 ∧ N.Tpipe - 1 < t ∧ t = N.Tpipe - 1 + N.L i) ↔ False :=
    ⟨fun h => by omega, False.elim⟩
  have hE : (i = c.sendTo ∧ N.Tpipe - 1 + N.L i < t + 1) ↔ (i = c.sendTo ∧ N.L i = 0) :=
    and_congr_right fun _ => by omega
  simp only [hB, hC, hE, if_false, add_zero]
  by_cases hL : N.L i = 0
  · have hl : (t < N.L i) ↔ False := ⟨fun h => by omega, False.elim⟩
    simp only [hL, hl, if_true, if_false, add_zero, and_true]
    by_cases hi : i = c.sendTo
    · simp only [hi, if_true]; ring
    · simp only [hi, if_false]; ring
  · simp only [hL, if_false, and_false]; ring

lemma prepI_step (d : ℕ → DemandVec n) (t : ℕ) (hT : t ≠ N.Tpipe - 1) (i : Fin n) :
    prepI N x c d t i + prepRet N x c t i t - ((d t i : ℝ≥0) : ℝ) = prepI N x c d (t + 1) i := by
  unfold prepI prepRet
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  by_cases hi : i = c.sendTo
  · rcases lt_trichotomy t (N.Tpipe - 1 + N.L i) with h | h | h
    · have f1 : (i = c.sendTo ∧ N.Tpipe - 1 + N.L i < t) ↔ False := ⟨fun h' => by omega, False.elim⟩
      have f2 : (i = c.sendTo ∧ N.L i ≠ 0 ∧ N.Tpipe - 1 < t ∧ t = N.Tpipe - 1 + N.L i) ↔ False :=
        ⟨fun h' => by omega, False.elim⟩
      have f3 : (i = c.sendTo ∧ N.Tpipe - 1 + N.L i < t + 1) ↔ False := ⟨fun h' => by omega, False.elim⟩
      simp only [f1, f2, f3, if_false]; ring
    · have f1 : (i = c.sendTo ∧ N.Tpipe - 1 + N.L i < t) ↔ False := ⟨fun h' => by omega, False.elim⟩
      have f2 : (i = c.sendTo ∧ N.L i ≠ 0 ∧ N.Tpipe - 1 < t ∧ t = N.Tpipe - 1 + N.L i) ↔ True :=
        ⟨fun _ => trivial, fun _ => ⟨hi, by omega, by omega, h⟩⟩
      have f3 : (i = c.sendTo ∧ N.Tpipe - 1 + N.L i < t + 1) ↔ True :=
        ⟨fun _ => trivial, fun _ => ⟨hi, by omega⟩⟩
      simp only [f1, f2, f3, if_false, if_true]; ring
    · have f1 : (i = c.sendTo ∧ N.Tpipe - 1 + N.L i < t) ↔ True := ⟨fun _ => trivial, fun _ => ⟨hi, h⟩⟩
      have f2 : (i = c.sendTo ∧ N.L i ≠ 0 ∧ N.Tpipe - 1 < t ∧ t = N.Tpipe - 1 + N.L i) ↔ False :=
        ⟨fun h' => by omega, False.elim⟩
      have f3 : (i = c.sendTo ∧ N.Tpipe - 1 + N.L i < t + 1) ↔ True :=
        ⟨fun _ => trivial, fun _ => ⟨hi, by omega⟩⟩
      simp only [f1, f2, f3, if_false, if_true]; ring
  · simp only [hi, false_and, if_false]; ring

lemma prepRet_step (t : ℕ) (hT : t ≠ N.Tpipe - 1) : prepRet N x c t = prepRet N x c (t + 1) := by
  funext i r
  unfold prepRet
  congr 1
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨a, b, e, f⟩; exact ⟨a, b, by omega, f⟩
  · rintro ⟨a, b, e, f⟩; exact ⟨a, b, by omega, f⟩

lemma prepRet_step_T (t : ℕ) (hT : t = N.Tpipe - 1) (i : Fin n) (r : ℕ) :
    (if N.L i = 0 then prepRet N x c t i else Function.update (prepRet N x c t i) (t + N.L i)
      (prepRet N x c t i (t + N.L i) + (if i = c.sendTo then W0 N x else 0))) r
      = prepRet N x c (t + 1) i r := by
  have hC : ∀ r', ¬ (i = c.sendTo ∧ N.L i ≠ 0 ∧ N.Tpipe - 1 < t ∧ r' = N.Tpipe - 1 + N.L i) :=
    fun r' h => by omega
  by_cases hL : N.L i = 0
  · rw [if_pos hL]
    unfold prepRet
    rw [if_neg (hC r), if_neg (show ¬ (i = c.sendTo ∧ N.L i ≠ 0 ∧ N.Tpipe - 1 < t + 1 ∧
      r = N.Tpipe - 1 + N.L i) from fun h => h.2.1 hL)]
  · rw [if_neg hL]
    by_cases hr : r = t + N.L i
    · subst hr
      rw [Function.update_self]
      unfold prepRet
      rw [if_neg (hC _), if_neg (show ¬ t + N.L i < N.L i by omega)]
      by_cases hi : i = c.sendTo
      · rw [if_pos hi, if_pos (show i = c.sendTo ∧ N.L i ≠ 0 ∧ N.Tpipe - 1 < t + 1 ∧
          t + N.L i = N.Tpipe - 1 + N.L i from ⟨hi, hL, by omega, by omega⟩)]
        ring
      · rw [if_neg hi, if_neg (show ¬ (i = c.sendTo ∧ N.L i ≠ 0 ∧ N.Tpipe - 1 < t + 1 ∧
          t + N.L i = N.Tpipe - 1 + N.L i) from fun h => hi h.1)]
        ring
    · rw [Function.update_of_ne hr]
      unfold prepRet
      rw [if_neg (hC r), if_neg (show ¬ (i = c.sendTo ∧ N.L i ≠ 0 ∧ N.Tpipe - 1 < t + 1 ∧
        r = N.Tpipe - 1 + N.L i) from fun h => hr (by omega))]

end prep

section prepRun

variable (N : Network n) (x : InitState n) (c : ConChoice n)
  (act : (ℕ → DemandVec n) → ℕ → Prop) [∀ d, DecidablePred (act d)]
  (hact : ∀ d t, act d t ↔ (N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
include hact

/-- The engine's start condition coincides with `act` during preparation. -/
lemma start_iff (d : ℕ → DemandVec n) (t : ℕ) :
    (N.Tpipe - 1 < t ∧ N.Tpipe - 1 + N.L c.sendTo ≤ t ∧
      ∀ i, (receive (prepState N x c d t) t).I i ≤ c.S i) ↔ act d t := by
  rw [hact]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, fun i => ?_⟩
    have := h3 i
    rwa [receive_prep_I N x c d t h1 h2] at this
  · rintro ⟨h1, h2⟩
    have h1' : N.Tpipe - 1 < t := by omega
    have h2' : N.Tpipe - 1 + N.L c.sendTo ≤ t := by omega
    exact ⟨h1', h2', fun i => by rw [receive_prep_I N x c d t h1' h2']; exact h2 i⟩

/-- During preparation the run is in the explicit preparation state. -/
lemma conRun_prep (d : ℕ → DemandVec n) : ∀ t, (∀ t' < t, ¬ act d t') →
    conRun N x c d t = prepState N x c d t
  | 0, _ => by
    have hW : prepW N x 0 = x.W := by simp [prepW]
    have hI : prepI N x c d 0 = x.I := by funext i; simp [prepI]
    have hR : prepRet N x c 0 = fun i r => if r < N.L i then x.retPipe i r else 0 := by
      funext i r; simp [prepRet]
    simp only [conRun, initEngState, prepState, hW, hI, hR]
  | t + 1, h => by
    have ih := conRun_prep d t (fun t' ht' => h t' (by omega))
    have hnot : ¬ act d t := h t (by omega)
    rw [conRun, ih]
    have hrun : (receive (prepState N x c d t) t).running = false := rfl
    have hcond : ¬ (N.Tpipe - 1 < t ∧ N.Tpipe - 1 + N.L c.sendTo ≤ t ∧
        ∀ i, (receive (prepState N x c d t) t).I i ≤ c.S i) :=
      fun hc => hnot ((start_iff N x c act hact d t).1 hc)
    unfold conStep
    simp only [hrun, Bool.false_eq_true, if_false]
    by_cases hT : t = N.Tpipe - 1
    · rw [if_pos hT]
      simp only [applyDemand, sendOut, receive, prepState]
      have hL0T := L0_le_Tpipe N
      have hWt : prepW N x t + (if t < N.L0 then x.supPipe t else 0) = W0 N x := by
        unfold prepW W0
        rw [if_pos (by omega), add_assoc]
        congr 1
        rw [← sum_ite_lt_eq x.supPipe N.L0 (t + 1) (by omega), Finset.sum_range_succ]
      rw [hWt]
      congr 1
      · simp only [prepW]; rw [if_neg (by omega)]
      · funext i
        have := prepI_step_T N x c d t hT i
        simp only [Pi.single_apply]
        exact this
      · funext i r
        have := prepRet_step_T N x c t hT i r
        simp only [Pi.single_apply]
        exact this
    · rw [if_neg hT, if_neg hcond]
      simp only [applyDemand, receive, prepState]
      have hL0T := L0_le_Tpipe N
      congr 1
      · unfold prepW
        by_cases h1 : t < N.Tpipe - 1
        · rw [if_pos (show t ≤ N.Tpipe - 1 by omega), if_pos (show t + 1 ≤ N.Tpipe - 1 by omega),
            Finset.sum_range_succ]; ring
        · rw [if_neg (show ¬ t ≤ N.Tpipe - 1 by omega), if_neg (show ¬ t + 1 ≤ N.Tpipe - 1 by omega),
            if_neg (show ¬ t < N.L0 by omega)]; ring
      · funext i
        exact prepI_step N x c d t hT i
      · exact prepRet_step N x c t hT

end prepRun

end OWMR.Eng


/-! Engine lemmas, part 7: the run of `π_con` from its start. -/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR


namespace OWMR.Eng

variable {n : ℕ}

/-- A new request. -/
def mkReq (i : Fin n) (Q θ : ℝ) (t : ℕ) : Req n :=
  { ret := i, size := Q, alloc := 0, shipped := 0, offset := θ, born := t }

section run

variable (N : Network n) (x : InitState n) (c : ConChoice n)
  (act : (ℕ → DemandVec n) → ℕ → Prop) [∀ d, DecidablePred (act d)]
  (Yp : (ℕ → DemandVec n) → ℕ → ℝ) (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
  (hact : ∀ d t, act d t ↔ (N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
  (hY0 : ∀ d, Yp d 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i))
  (hY : ∀ d t, Yp d (t + 1) = (if act d t ∧ Yp d t ≤ c.s0 then c.S0 else Yp d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
  (hPh0 : ∀ d i, Ph d 0 i = c.S i)
  (hPh : ∀ d t i, Ph d (t + 1) i = if act d t then
      (if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i else Ph d t i - ((d t i : ℝ≥0) : ℝ))
      else c.S i)
  (hq : ∀ d t i, q d t i = if act d t then
      (if t = 0 ∨ ¬ act d (t - 1) then
        c.S i - (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
          - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
      else if Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i then
        c.S i - (Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ)) else 0)
    else 0)

include hact in
lemma act_time (d : ℕ → DemandVec n) (t : ℕ) (h : act d t) :
    1 ≤ t ∧ N.L0 ≤ t ∧ N.Tpipe - 1 < t ∧ N.Tpipe - 1 + N.L c.sendTo ≤ t := by
  have h1 := ((hact d t).1 h).1
  have h2 := L0_le_Tpipe N
  have h3 : 1 ≤ max 1 (N.L c.sendTo) := le_max_left _ _
  have h4 : N.L c.sendTo ≤ max 1 (N.L c.sendTo) := le_max_right _ _
  refine ⟨by omega, by omega, by omega, by omega⟩

include hact in
lemma act_mono (d : ℕ → DemandVec n) (t : ℕ) (h : act d t) : act d (t + 1) := by
  rw [hact] at h ⊢
  refine ⟨by omega, fun i => ?_⟩
  have := h.2 i
  rw [Finset.sum_range_succ]
  linarith [NNReal.coe_nonneg (d t i)]

include hact in
lemma act_mono' (d : ℕ → DemandVec n) {t t' : ℕ} (htt : t ≤ t') (h : act d t) : act d t' := by
  induction htt with
  | refl => exact h
  | step _ ih => exact act_mono N x c act hact d _ ih

include hact in
lemma not_act_zero (d : ℕ → DemandVec n) : ¬ act d 0 := fun h =>
  absurd (act_time N x c act hact d 0 h).1 (by omega)

include hact in
lemma act_IPx (d : ℕ → DemandVec n) (t : ℕ) (h : act d t) (i : Fin n) :
    IPx N x c d t i ≤ c.S i := ((hact d t).1 h).2 i

include hact hq in
lemma q_zero (d : ℕ → DemandVec n) (t : ℕ) (h : ¬ act d t) (i : Fin n) : q d t i = 0 := by
  rw [hq, if_neg h]

include hact hq hsS in
lemma q_nonneg (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : 0 ≤ q d t i := by
  rw [hq]
  by_cases h1 : act d t
  · rw [if_pos h1]
    by_cases h2 : t = 0 ∨ ¬ act d (t - 1)
    · rw [if_pos h2]
      have := act_IPx N x c act hact d t h1 i
      unfold IPx at this
      linarith
    · rw [if_neg h2]
      by_cases h3 : Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i
      · rw [if_pos h3]; linarith [hsS i]
      · rw [if_neg h3]
  · rw [if_neg h1]

include hact hq in
lemma q_start (d : ℕ → DemandVec n) (t : ℕ) (h : act d t) (h' : ¬ act d (t - 1)) (i : Fin n) :
    q d t i = c.S i - IPx N x c d t i := by
  rw [hq, if_pos h, if_pos (Or.inr h')]
  rfl

include hact hq in
lemma q_ord (d : ℕ → DemandVec n) (t : ℕ) (h : act d t) (i : Fin n) :
    q d (t + 1) i = if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then
      c.S i - (Ph d t i - ((d t i : ℝ≥0) : ℝ)) else 0 := by
  rw [hq, if_pos (act_mono N x c act hact d t h),
    if_neg (by simp only [add_tsub_cancel_right]; push Not; exact ⟨by omega, h⟩)]
  simp only [add_tsub_cancel_right]

include hact in
lemma q0x_zero (d : ℕ → DemandVec n) (t : ℕ) (h : ¬ act d t) : q0x c act Yp d t = 0 := by
  unfold q0x; rw [if_neg (fun h' => h h'.1)]

include hact hY0 hY in
/-- Before the start, the supplier position is the initial one minus demand. -/
lemma Yp_prep (d : ℕ → DemandVec n) : ∀ t, (∀ t' < t, ¬ act d t') →
    Yp d t = ∑ i, (IPx N x c d t i - c.S i)
  | 0, _ => by
    rw [hY0]
    unfold IPx
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
    rw [Finset.sum_congr rfl (fun i _ => show x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0) - c.S i
      = (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i)
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0) by ring),
      Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ c.sendTo]
    simp only [Finset.mem_univ, if_true]
    ring
  | t + 1, h => by
    rw [hY, if_neg (fun h' => h t (by omega) h'.1),
      Yp_prep d t (fun t' ht' => h t' (by omega))]
    unfold IPx
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ]
    ring

/-- The state after the receipts of period `t`, with the initial requests in the start period. -/
def preA (d : ℕ → DemandVec n) (t : ℕ) : EngState n :=
  if (receive (conRun N x c d t) t).running then receive (conRun N x c d t) t
  else startWith (receive (conRun N x c d t) t) t
    (fun i => c.S i - (receive (conRun N x c d t) t).I i) c.initOffset

/-- The state after step 2 (requests and the supplier order) of a running period. -/
def postA (d : ℕ → DemandVec n) (t : ℕ) : EngState n :=
  (phaseA N.L0 N.L c.params (conRule N c) t (preA N x c d t)).1

include hact in
lemma not_act_before (d : ℕ → DemandVec n) (t : ℕ) (h : ¬ (0 < t ∧ act d (t - 1))) :
    ∀ t' < t, ¬ act d t' := by
  intro t' ht' ha
  exact h ⟨by omega, act_mono' N x c act hact d (show t' ≤ t - 1 by omega) ha⟩

include hact in
/-- The policy runs in period `t` exactly when `act` held in the previous period. -/
lemma running_iff (d : ℕ → DemandVec n) : ∀ t,
    (conRun N x c d t).running = true ↔ (0 < t ∧ act d (t - 1))
  | 0 => by simp [conRun, initEngState]
  | t + 1 => by
    have ih := running_iff d t
    simp only [add_tsub_cancel_right, show 0 < t + 1 by omega, true_and]
    rw [conRun]
    simp only [applyDemand_running]
    unfold conStep
    by_cases hr : (conRun N x c d t).running = true
    · have hr' : (receive (conRun N x c d t) t).running = true := hr
      simp only [hr', if_true]
      have ha := ih.1 hr
      refine ⟨fun _ => act_mono' N x c act hact d (show t - 1 ≤ t by omega) ha.2, fun _ => ?_⟩
      have e : (runStep N.L0 N.L c.params (conRule N c) t (receive (conRun N x c d t) t)).1.running
          = (receive (conRun N x c d t) t).running := rfl
      rw [e]; exact hr'
    · have hr' : (receive (conRun N x c d t) t).running = false := by
        simpa using hr
      simp only [hr', Bool.false_eq_true, if_false]
      have hpre := not_act_before N x c act hact d t (fun h => hr (ih.2 h))
      have hrun := conRun_prep N x c act hact d t hpre
      by_cases hT : t = N.Tpipe - 1
      · rw [if_pos hT]
        constructor
        · intro h; exact absurd h (by simp [sendOut])
        · intro h; exact absurd (act_time N x c act hact d t h).2.2.1 (by omega)
      · rw [if_neg hT]
        by_cases hc : N.Tpipe - 1 < t ∧ N.Tpipe - 1 + N.L c.sendTo ≤ t ∧
            ∀ i, (receive (conRun N x c d t) t).I i ≤ c.S i
        · rw [if_pos hc]
          rw [hrun] at hc
          refine ⟨fun _ => (start_iff N x c act hact d t).1 hc, fun _ => rfl⟩
        · rw [if_neg hc]
          rw [hrun] at hc
          refine ⟨fun h => absurd h (by simp [hrun, prepState]), fun h => ?_⟩
          exact absurd ((start_iff N x c act hact d t).2 h) hc

include hact in
/-- In a period where `act` holds, the policy performs a running period from `preA`. -/
lemma conStep_act (d : ℕ → DemandVec n) (t : ℕ) (h : act d t) :
    conStep N c t (conRun N x c d t) = runStep N.L0 N.L c.params (conRule N c) t (preA N x c d t) := by
  unfold conStep preA
  by_cases hr : (conRun N x c d t).running = true
  · have hr' : (receive (conRun N x c d t) t).running = true := hr
    simp only [hr', if_true]
  · have hr' : (receive (conRun N x c d t) t).running = false := by simpa using hr
    simp only [hr', Bool.false_eq_true, if_false]
    have hpre := not_act_before N x c act hact d t (fun h' => hr ((running_iff N x c act hact d t).2 h'))
    have hrun := conRun_prep N x c act hact d t hpre
    have ht := act_time N x c act hact d t h
    rw [if_neg (by omega)]
    have hc : N.Tpipe - 1 < t ∧ N.Tpipe - 1 + N.L c.sendTo ≤ t ∧
        ∀ i, (receive (conRun N x c d t) t).I i ≤ c.S i := by
      rw [hrun]; exact (start_iff N x c act hact d t).2 h
    rw [if_pos hc]

include hact in
lemma conRun_succ_act (d : ℕ → DemandVec n) (t : ℕ) (h : act d t) :
    conRun N x c d (t + 1) = applyDemand (phaseB N.L c.params t (postA N x c d t)).1 (d t) := by
  rw [conRun, conStep_act N x c act hact d t h]
  rfl

include hact in
lemma preA_succ (d : ℕ → DemandVec n) (t : ℕ) (h : act d t) :
    preA N x c d (t + 1) = receive (conRun N x c d (t + 1)) (t + 1) := by
  unfold preA
  have : (receive (conRun N x c d (t + 1)) (t + 1)).running = true :=
    (running_iff N x c act hact d (t + 1)).2 ⟨by omega, by simpa using h⟩
  rw [if_pos this]

include hact in
/-- The recursion of the post-step-2 states. -/
lemma postA_succ (d : ℕ → DemandVec n) (t : ℕ) (h : act d t) :
    postA N x c d (t + 1) = (phaseA N.L0 N.L c.params (conRule N c) (t + 1)
      (receive (applyDemand (phaseB N.L c.params t (postA N x c d t)).1 (d t)) (t + 1))).1 := by
  rw [postA, preA_succ N x c act hact d t h, conRun_succ_act N x c act hact d t h]

/-! ### The start period -/

include hact in
lemma start_facts (d : ℕ → DemandVec n) (t : ℕ) (h : act d t) (hpre : ∀ t' < t, ¬ act d t') :
    let st := receive (prepState N x c d t) t
    st.running = false ∧ st.Wbar = 0 ∧ (∀ i, st.I i = IPx N x c d t i) ∧
    (∀ r, t < r → st.supPipe r = 0) ∧ (∀ i r, t < r → st.retPipe i r = 0) ∧
    st.queue = [] ∧ st.nOrd = 0 := by
  intro st
  have ht := act_time N x c act hact d t h
  have hL0 := L0_le_Tpipe N
  refine ⟨rfl, ?_, fun i => receive_prep_I N x c d t ht.2.2.1 ht.2.2.2 i, fun r hr => ?_,
    fun i r hr => ?_, rfl, rfl⟩
  · show prepW N x t + (if t < N.L0 then x.supPipe t else 0) = 0
    unfold prepW
    rw [if_neg (by omega), if_neg (by omega), add_zero]
  · show (if r < N.L0 then x.supPipe r else 0) = 0
    rw [if_neg (by omega)]
  · show prepRet N x c t i r = 0
    unfold prepRet
    have := L_le_Tpipe N i
    rw [if_neg (by omega), if_neg (fun h' => by obtain ⟨rfl, -, -, h4⟩ := h'; omega), add_zero]

include hact hq hsS hY0 hY hPh in
/-- The state after step 2 of the start period satisfies the projected invariant. -/
lemma inv_start (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (t : ℕ) (h : act d t)
    (hpre : ∀ t' < t, ¬ act d t') :
    InvP N c act Yp Ph q d t (postA N x c d t) ∧
      (phaseA N.L0 N.L c.params (conRule N c) t (preA N x c d t)).2 = q0x c act Yp d t := by
  have ht := act_time N x c act hact d t h
  have hpre' : ¬ act d (t - 1) := hpre (t - 1) (by omega)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := start_facts N x c act hact d t h hpre
  have hrun := conRun_prep N x c act hact d t hpre
  have hsz : (fun i => c.S i - (receive (prepState N x c d t) t).I i) = q d t := by
    funext i; rw [f3, q_start N x c act Ph q hact hq d t h hpre']
  have hpreA : preA N x c d t = startWith (receive (prepState N x c d t) t) t (q d t)
      c.initOffset := by
    unfold preA; rw [hrun, if_neg (by rw [f1]; decide), hsz]
  set st := receive (prepState N x c d t) t with hst
  set st' := startWith st t (q d t) c.initOffset with hst'
  have hq0 := q_nonneg N x c act Ph q hsS hact hq d
  have hqz : ∀ s < t, ∀ i, q d s i = 0 := fun s hs i =>
    q_zero N x c act Ph q hact hq d s (hpre s hs) i
  have hstq : st'.queue = ((List.finRange n).filter (fun i => decide (0 < q d t i))).map
      (fun i => mkReq i (q d t i) (c.initOffset i) t) := by
    simp only [hst', startWith, f6, List.nil_append]
    rfl
  -- inventories, positions and requests in the start period
  have hphys : ∀ i, physPos N.L st' t i = IPx N x c d t i := fun i => by
    show st.I i + ∑ k ∈ Finset.range (N.L i), st.retPipe i (t + 1 + k) = _
    rw [f3, Finset.sum_eq_zero fun k _ => f5 i _ (by omega), add_zero]
  have hqt : ∀ i, qterm st'.queue i (fun r => r.size - r.shipped)
      = if 0 < q d t i then q d t i else 0 := fun i => by
    rw [qterm_eq_map, hstq, List.map_map]
    rw [show ((fun r : Req n => if r.ret = i then r.size - r.shipped else 0) ∘
        (fun i => mkReq i (q d t i) (c.initOffset i) t)) = fun j => if j = i then q d t j else 0 by
      funext j; simp [mkReq]]
    rw [sum_map_ite_eq_nodup _ _ _ ((List.nodup_finRange n).filter _)]
    simp [List.mem_filter]
  have hphat : ∀ i, phat N.L st' t i = c.S i := fun i => by
    rw [phat_eq, hphys, hqt, q_start N x c act Ph q hact hq d t h hpre']
    have := act_IPx N x c act hact d t h i
    by_cases h' : 0 < c.S i - IPx N x c d t i
    · rw [if_pos h']; ring
    · rw [if_neg h']; linarith
  have hreq : ∀ i, reqSize N.L c.params st' t i = 0 := fun i => by
    unfold reqSize; rw [hphat]
    show (if c.S i ≤ c.s i then c.S i - c.S i else 0) = 0
    split_ifs <;> ring
  have hnew : newRA N.L0 N.L c.params (conRule N c) t st' = [] := by
    unfold newRA
    rw [List.mapIdx_eq_nil_iff, List.filter_eq_nil_iff]
    intro i _
    simp [hreq]
  have hres : ∑ i, reserve st' i = 0 := by
    rw [sum_reserve, hstq, List.map_map]
    exact List.sum_eq_zero fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      simp [mkReq]
  have hsupT : supInTransit N.L0 st' t = 0 :=
    Finset.sum_eq_zero fun k _ => f4 _ (by omega)
  have hYp : Yp d t = ∑ i, (IPx N x c d t i - c.S i) :=
    Yp_prep N x c act Yp hact hY0 hY d t hpre
  have hposst : posE N.L0 N.L c.S st' t = Yp d t := by
    unfold posE
    rw [hres, hsupT, hYp]
    simp only [hphys]
    show st.Wbar + 0 + 0 + _ = _
    rw [f2]; ring
  have hq0' : (phaseA N.L0 N.L c.params (conRule N c) t st').2 = q0x c act Yp d t := by
    rw [phaseA_snd]
    show (if posE N.L0 N.L c.S st' t ≤ c.s0 then c.S0 - posE N.L0 N.L c.S st' t else 0) = _
    rw [hposst]; unfold q0x; simp only [h, true_and]
  have hpost : postA N x c d t = (phaseA N.L0 N.L c.params (conRule N c) t st').1 := by
    unfold postA; rw [hpreA]
  -- explicit data before the start
  have hVt1 : Vx N c act Yp d (t - 1) = 0 :=
    Finset.sum_eq_zero fun r hr => q0x_zero N x c act Yp hact d r (hpre r (by
      simp only [Finset.mem_range] at hr; omega))
  have hPq : Pq (q d) t = 0 := Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun j _ =>
    hqz r (Finset.mem_range.1 hr) j
  have hVt : Vx N c act Yp d t = if N.L0 = 0 then q0x c act Yp d t else 0 := by
    unfold Vx
    by_cases h0 : N.L0 = 0
    · rw [if_pos h0, h0, Nat.sub_zero, Finset.sum_range_succ,
        Finset.sum_eq_zero fun r hr => q0x_zero N x c act Yp hact d r (hpre r (Finset.mem_range.1 hr)),
        zero_add]
    · rw [if_neg h0]
      exact Finset.sum_eq_zero fun r hr => q0x_zero N x c act Yp hact d r (hpre r (by
        simp only [Finset.mem_range] at hr; omega))
  have hLall : Lall (q d) t = perL (q d) t := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [Lall_succ]
    have : Lall (q d) t' = [] := by
      unfold Lall
      rw [List.flatMap_eq_nil_iff]
      intro s hs
      unfold perL
      rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
      intro i _
      rw [hqz s (by simp only [List.mem_range] at hs; omega) i]
      simp
    rw [this, List.nil_append]
  have hLpre : Lpre N c act Yp q d t = perL (q d) t := by
    unfold Lpre
    rw [hLall]
    refine List.filter_eq_self.2 fun k hk => ?_
    rw [mem_perL] at hk
    simp [hk.1]
  refine ⟨?_, by rw [hpreA]; exact hq0'⟩
  rw [hpost, phaseA_fst]
  constructor
  · -- unallocated warehouse stock
    show (if N.L0 = 0 then st'.Wbar + (phaseA N.L0 N.L c.params (conRule N c) t st').2 else st'.Wbar)
      = _
    rw [hq0', hVt1, hPq, hVt]
    have : st'.Wbar = 0 := f2
    rw [this]
    split_ifs <;> simp
  · -- scheduled supplier receipts
    intro r hr
    show (if N.L0 = 0 then st'.supPipe else Function.update st'.supPipe (t + N.L0)
      (st'.supPipe (t + N.L0) + (phaseA N.L0 N.L c.params (conRule N c) t st').2)) r = _
    rw [hq0']
    have hs' : ∀ r', t < r' → st'.supPipe r' = 0 := f4
    by_cases h0 : N.L0 = 0
    · rw [if_pos h0, hs' r hr, if_neg (by omega)]
    · rw [if_neg h0]
      by_cases hr' : r = t + N.L0
      · subst hr'
        rw [Function.update_self, hs' _ (by omega), zero_add, if_pos ⟨by omega, le_rfl⟩,
          show t + N.L0 - N.L0 = t by omega]
      · rw [Function.update_of_ne hr', hs' r hr]
        by_cases hr2 : r ≤ t + N.L0
        · rw [if_pos ⟨by omega, hr2⟩, q0x_zero N x c act Yp hact d _ (hpre _ (by omega))]
        · rw [if_neg (fun h' => hr2 h'.2)]
  · -- the queue keys
    show (st'.queue ++ newRA N.L0 N.L c.params (conRule N c) t st').map key = _
    rw [hnew, List.append_nil, hstq, hLpre, List.map_map]
    rfl
  · -- the requests
    intro r hr
    have hr' : r ∈ st'.queue := by
      have : r ∈ st'.queue ++ newRA N.L0 N.L c.params (conRule N c) t st' := hr
      rwa [hnew, List.append_nil] at this
    rw [hstq] at hr'
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr'
    refine ⟨rfl, ?_, le_rfl, le_rfl⟩
    show (0 : ℝ) = max 0 (min (q d t i) (min (Vx N c act Yp d (t - 1)) (Pq (q d) t) - ahx (q d) t i))
    rw [hVt1, hPq, min_self, zero_sub]
    have := ahx_nonneg (q d) (hq0) t i
    rw [hPq] at this
    rw [max_eq_left (min_le_of_right_le (by linarith))]
  · -- positions including outstanding requests
    intro i
    have := phat_phaseA N.L0 N.L c.params (conRule N c) t st' i
    rw [phaseA_fst] at this
    rw [this, hphat, hreq, if_neg (lt_irrefl 0), add_zero]
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [hPh, if_neg (by simpa using hpre')]
  · -- no shipments beyond the lead time
    intro i r hr
    exact f5 i r (by omega)
  · -- ordinary request count
    show st'.nOrd + _ = _
    rw [show st'.nOrd = 0 from f7]
    have : ((List.finRange n).filter (fun i => decide (0 < reqSize N.L c.params st' t i))).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro i _
      simp [hreq]
    rw [this]
    unfold nOx
    symm
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hpre (r - 1) (by simp only [Finset.mem_range] at hr; omega) h2
  · -- the supplier position after the order
    have := posE_phaseA N.L0 N.L c.params (conRule N c) t st'
    rw [phaseA_fst] at this
    show posE N.L0 N.L c.S _ t = _
    have e : c.params.center = c.S := rfl
    rw [e] at this
    rw [this, hposst, hq0']
    unfold Ypost q0x
    simp only [h, true_and]
    split_ifs <;> ring

include hact hq hsS hY0 hY hPh in
/-- The projected invariant and the supplier orders along the whole run. -/
theorem inv_all (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) : ∀ t, act d t →
    InvP N c act Yp Ph q d t (postA N x c d t) ∧
      (phaseA N.L0 N.L c.params (conRule N c) t (preA N x c d t)).2 = q0x c act Yp d t
  | 0, h => absurd h (not_act_zero N x c act hact d)
  | t + 1, h => by
    by_cases h' : act d t
    · have ih := (inv_all hs0S d t h').1
      have ht := act_time N x c act hact d t h'
      have hgen := step_generic N c act Yp Ph q (q_nonneg N x c act Ph q hsS hact hq) hs0S hY hPh
        (fun d t i ha => q_ord N x c act Ph q hact hq d t ha i)
        (fun d t ha => act_mono N x c act hact d t ha)
        (fun d t ha => (act_time N x c act hact d t ha).2.1)
        d t ht.1 h' (postA N x c d t) ih c.params c.params ⟨rfl, rfl, rfl, rfl, rfl⟩ (conRule N c)
      rw [← postA_succ N x c act hact d t h'] at hgen
      refine ⟨hgen.1, ?_⟩
      rw [preA_succ N x c act hact d t h', conRun_succ_act N x c act hact d t h']
      exact hgen.2
    · exact inv_start N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S d (t + 1) h
        (fun t' ht' ha => h' (act_mono' N x c act hact d (show t' ≤ t by omega) ha))

end run

end OWMR.Eng


/-! Engine lemmas, part 8: offsets and shipments of the actual run. -/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR


namespace OWMR.Eng

variable {n : ℕ}

lemma find_key (l : List (Req n)) (hl : (l.map key).Nodup) (r : Req n) (hr : r ∈ l) :
    l.find? (fun y => decide (y.born = r.born ∧ y.ret = r.ret)) = some r := by
  have hs : (l.find? (fun y => decide (y.born = r.born ∧ y.ret = r.ret))).isSome :=
    List.find?_isSome.2 ⟨r, hr, by simp⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  rw [hy]
  have hym := List.mem_of_find?_eq_some hy
  have hyp := List.find?_some hy
  simp only [decide_eq_true_eq] at hyp
  congr 1
  exact List.inj_on_of_nodup_map hl hym hr (by simp [key, hyp.1, hyp.2])

lemma conRule_mem (N : Network n) (c : ConChoice n) (σ : EngState n) (t j : ℕ) (i : Fin n)
    (Q : ℝ) : 0 < conRule N c σ t j i Q ∧ conRule N c σ t j i Q < 1 := by
  unfold conRule
  dsimp only
  split_ifs with h
  · exact ⟨by exact_mod_cast (c.enum (Nat.find h)).2.1,
      by exact_mod_cast (c.enum (Nat.find h)).2.2⟩
  · norm_num

/-- Offsets of the new requests of step 2. -/
lemma newRA_offset (L0 : ℕ) (L : Fin n → ℕ) (P : EngParams n) (rule : OffsetRule n) (t : ℕ)
    (st : EngState n) : ∀ r ∈ newRA L0 L P rule t st,
    r.offset = if P.batch r.ret then rule
          { st with
            Wbar := if L0 = 0 then st.Wbar + (phaseA L0 L P rule t st).2 else st.Wbar
            supPipe := if L0 = 0 then st.supPipe
              else Function.update st.supPipe (t + L0)
                (st.supPipe (t + L0) + (phaseA L0 L P rule t st).2)
            queue := st.queue ++ ((List.finRange n).filter
              (fun i => decide (0 < reqSize L P st t i))).map (fun i =>
                ({ ret := i, size := reqSize L P st t i, alloc := 0, shipped := 0, offset := 0,
                   born := t } : Req n))
            nOrd := st.nOrd + ((List.finRange n).filter
              (fun i => decide (0 < reqSize L P st t i))).length }
          t (st.nOrd + ((List.finRange n).filter
              (fun i => decide (0 < reqSize L P st t i))).idxOf r.ret + 1) r.ret
          (reqSize L P st t r.ret) else 0 := by
  intro r hr
  unfold newRA at hr
  obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.1 hr
  dsimp only
  have hnd := (List.nodup_finRange n).filter (fun i => decide (0 < reqSize L P st t i))
  have e : ((List.finRange n).filter (fun i => decide (0 < reqSize L P st t i))).idxOf
      ((List.finRange n).filter (fun i => decide (0 < reqSize L P st t i)))[k] = k :=
    List.get_idxOf hnd ⟨k, hk⟩
  rw [e]

section ship

variable (N : Network n) (x : InitState n) (c : ConChoice n)
  (act : (ℕ → DemandVec n) → ℕ → Prop) [∀ d, DecidablePred (act d)]
  (Yp : (ℕ → DemandVec n) → ℕ → ℝ) (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
  (hact : ∀ d t, act d t ↔ (N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
  (hY0 : ∀ d, Yp d 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i))
  (hY : ∀ d t, Yp d (t + 1) = (if act d t ∧ Yp d t ≤ c.s0 then c.S0 else Yp d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
  (hPh0 : ∀ d i, Ph d 0 i = c.S i)
  (hPh : ∀ d t i, Ph d (t + 1) i = if act d t then
      (if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i else Ph d t i - ((d t i : ℝ≥0) : ℝ))
      else c.S i)
  (hq : ∀ d t i, q d t i = if act d t then
      (if t = 0 ∨ ¬ act d (t - 1) then
        c.S i - (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
          - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
      else if Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i then
        c.S i - (Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ)) else 0)
    else 0)


/-- Cumulative allocation of request `(s,i)` after the allocation of period `t`. -/
def Ax (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) : ℝ :=
  max 0 (min (q d s i) (Vx N c act Yp d t - ahx (q d) s i))

/-- The offset of request `(s,i)` in the actual run. -/
def θx (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) : ℝ :=
  if c.batch i = true ∧ act d s ∧ 0 < q d s i then
    ((postA N x c d s).queue.find? (fun r => decide (r.born = s ∧ r.ret = i))).elim (1 / 2)
      (fun r => r.offset)
  else 1 / 2

/-- Quantity of request `(s,i)` shipped by the end of period `t`. -/
def shx (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) : ℝ :=
  if t < s then 0 else if c.batch i then
    shippedPath (q d s i) (θx N x c act q d s i) (fun k => Ax N c act Yp q d s i (s + k)) (t - s)
  else Ax N c act Yp q d s i t

/-- The shipment invariant of the actual run. -/
structure InvS (d : ℕ → DemandVec n) (t : ℕ) (Z : EngState n) : Prop where
  ship : ∀ r ∈ Z.queue, r.shipped =
    if r.born < t then shx N x c act Yp q d r.born r.ret (t - 1) else 0
  off : ∀ r ∈ Z.queue, c.batch r.ret = true →
    r.offset = θx N x c act q d r.born r.ret ∧ 0 < r.offset ∧ r.offset < 1

lemma Lpre_nodup (hq0 : ∀ d s i, 0 ≤ q d s i) (d : ℕ → DemandVec n) (t : ℕ) :
    (Lpre N c act Yp q d t).Nodup :=
  (Lall_nodup (q d) (hq0 d) t).filter _

lemma θx_of_mem (hq0 : ∀ d s i, 0 ≤ q d s i) (d : ℕ → DemandVec n) (s : ℕ) (hs : act d s)
    (hI : InvP N c act Yp Ph q d s (postA N x c d s)) (r : Req n)
    (hr : r ∈ (postA N x c d s).queue) (hb : r.born = s) (hbat : c.batch r.ret = true) :
    θx N x c act q d s r.ret = r.offset := by
  have hpos : 0 < q d s r.ret := by
    have := (hI.elems r hr).1
    have hk : key r ∈ Lpre N c act Yp q d s := by rw [← hI.keys]; exact List.mem_map_of_mem hr
    unfold Lpre at hk
    rw [List.mem_filter, mem_Lall] at hk
    rw [← hb]; exact hk.1.2
  unfold θx
  rw [if_pos ⟨hbat, hs, hpos⟩]
  have hnd : ((postA N x c d s).queue.map key).Nodup := by
    rw [hI.keys]; exact Lpre_nodup N c act Yp q hq0 d s
  have := find_key _ hnd r hr
  rw [hb] at this
  rw [this]
  rfl

/-- Shipments in a period follow `shippedPath` along the cumulative allocations. -/
lemma ship_step (hq0 : ∀ d s i, 0 ≤ q d s i) (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n)
    (t : ℕ) (ht1 : 1 ≤ t) (Z : EngState n) (hI : InvP N c act Yp Ph q d t Z)
    (hS : InvS N x c act Yp q d t Z) (r : Req n) (hr : r ∈ Z.queue) :
    (serveElem c.params.batch (Vx N c act Yp d t) r (ahx (q d) r.born r.ret)).shipped
      = shx N x c act Yp q d r.born r.ret t := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := elem_facts N c act Yp Ph q hq0 hs0S d t ht1 Z hI r hr
  obtain ⟨hsz, halloc, -, -⟩ := hI.elems r hr
  have hk : key r ∈ Lpre N c act Yp q d t := by rw [← hI.keys]; exact List.mem_map_of_mem hr
  unfold Lpre at hk
  rw [List.mem_filter, mem_Lall] at hk
  obtain ⟨⟨hkt, hkq⟩, hkp0⟩ := hk
  have hkp : r.born = t ∨ Vx N c act Yp d (t - 1) < ahx (q d) r.born r.ret + q d r.born r.ret :=
    of_decide_eq_true hkp0
  simp only [key] at hkt hkq
  have hA' : max 0 (min r.size (Vx N c act Yp d t - ahx (q d) r.born r.ret))
      = Ax N c act Yp q d r.born r.ret t := by rw [hsz]; rfl
  have hsh := hS.ship r hr
  unfold shx
  rw [if_neg (not_lt.2 hkt)]
  have hS0 : (serveElem c.params.batch (Vx N c act Yp d t) r (ahx (q d) r.born r.ret)).shipped
      = if c.batch r.ret = false ∨ crossesThreshold r.size r.offset r.alloc
          (Ax N c act Yp q d r.born r.ret t)
        then Ax N c act Yp q d r.born r.ret t else r.shipped := by
    unfold serveElem; dsimp only; rw [hA']; rfl
  rw [hS0]
  by_cases hb : c.batch r.ret = true
  · have hθ := (hS.off r hr hb).1
    rw [if_pos hb, hsz, hθ]
    simp only [hb, Bool.true_eq_false, false_or]
    rcases eq_or_lt_of_le hkt with heq | hlt
    · -- created in this period
      have hal0 : r.alloc = 0 := by
        rw [halloc]
        have := ahx_nonneg (q d) (hq0 d) r.born r.ret
        rw [heq] at this ⊢
        rw [max_eq_left (min_le_of_right_le (by
          linarith [min_le_right (Vx N c act Yp d (t - 1)) (Pq (q d) t)]))]
      have hsh' : r.shipped = 0 := by rw [hsh, if_neg (by omega)]
      rw [hsh', hal0, heq, Nat.sub_self]
      simp only [shippedPath, add_zero]
    · -- created earlier and still pending
      have hpend : Vx N c act Yp d (t - 1) < ahx (q d) r.born r.ret + q d r.born r.ret :=
        hkp.resolve_left (by omega)
      have hle : ahx (q d) r.born r.ret + q d r.born r.ret ≤ Pq (q d) t :=
        (ahx_add_le (q d) (hq0 d) r.born r.ret).trans (Pq_mono (q d) (hq0 d) (by omega))
      have hal : r.alloc = Ax N c act Yp q d r.born r.ret (t - 1) := by
        rw [halloc, min_eq_left (show Vx N c act Yp d (t - 1) ≤ Pq (q d) t by linarith), hsz]; rfl
      rw [hsh, if_pos hlt, hal]
      unfold shx
      rw [if_neg (show ¬ (t - 1 < r.born) by omega), if_pos hb]
      obtain ⟨k, hk⟩ : ∃ k, t - r.born = k + 1 := ⟨t - 1 - r.born, by omega⟩
      rw [hk, show t - 1 - r.born = k by omega]
      simp only [shippedPath]
      rw [show r.born + k = t - 1 by omega, show r.born + (k + 1) = t by omega]
  · have hb' : c.batch r.ret = false := by simpa using hb
    rw [if_neg hb]
    simp only [hb', true_or, if_true]

include hact hq hsS in
/-- The queue after step 2 of the start period consists of the initial requests. -/
lemma postA_start_queue (d : ℕ → DemandVec n) (t : ℕ) (h : act d t)
    (hpre : ∀ t' < t, ¬ act d t') :
    (postA N x c d t).queue = ((List.finRange n).filter (fun i => decide (0 < q d t i))).map
      (fun i => mkReq i (q d t i) (c.initOffset i) t) := by
  have ht := act_time N x c act hact d t h
  have hpre' : ¬ act d (t - 1) := hpre (t - 1) (by omega)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := start_facts N x c act hact d t h hpre
  have hrun := conRun_prep N x c act hact d t hpre
  have hsz : (fun i => c.S i - (receive (prepState N x c d t) t).I i) = q d t := by
    funext i; rw [f3, q_start N x c act Ph q hact hq d t h hpre']
  have hpreA : preA N x c d t = startWith (receive (prepState N x c d t) t) t (q d t)
      c.initOffset := by
    unfold preA; rw [hrun, if_neg (by rw [f1]; decide), hsz]
  set st := receive (prepState N x c d t) t with hst
  set st' := startWith st t (q d t) c.initOffset with hst'
  have hq0 := q_nonneg N x c act Ph q hsS hact hq d
  have hqz : ∀ s < t, ∀ i, q d s i = 0 := fun s hs i =>
    q_zero N x c act Ph q hact hq d s (hpre s hs) i
  have hstq : st'.queue = ((List.finRange n).filter (fun i => decide (0 < q d t i))).map
      (fun i => mkReq i (q d t i) (c.initOffset i) t) := by
    simp only [hst', startWith, f6, List.nil_append]
    rfl
  -- inventories, positions and requests in the start period
  have hphys : ∀ i, physPos N.L st' t i = IPx N x c d t i := fun i => by
    show st.I i + ∑ k ∈ Finset.range (N.L i), st.retPipe i (t + 1 + k) = _
    rw [f3, Finset.sum_eq_zero fun k _ => f5 i _ (by omega), add_zero]
  have hqt : ∀ i, qterm st'.queue i (fun r => r.size - r.shipped)
      = if 0 < q d t i then q d t i else 0 := fun i => by
    rw [qterm_eq_map, hstq, List.map_map]
    rw [show ((fun r : Req n => if r.ret = i then r.size - r.shipped else 0) ∘
        (fun i => mkReq i (q d t i) (c.initOffset i) t)) = fun j => if j = i then q d t j else 0 by
      funext j; simp [mkReq]]
    rw [sum_map_ite_eq_nodup _ _ _ ((List.nodup_finRange n).filter _)]
    simp [List.mem_filter]
  have hphat : ∀ i, phat N.L st' t i = c.S i := fun i => by
    rw [phat_eq, hphys, hqt, q_start N x c act Ph q hact hq d t h hpre']
    have := act_IPx N x c act hact d t h i
    by_cases h' : 0 < c.S i - IPx N x c d t i
    · rw [if_pos h']; ring
    · rw [if_neg h']; linarith
  have hreq : ∀ i, reqSize N.L c.params st' t i = 0 := fun i => by
    unfold reqSize; rw [hphat]
    show (if c.S i ≤ c.s i then c.S i - c.S i else 0) = 0
    split_ifs <;> ring
  have hnew : newRA N.L0 N.L c.params (conRule N c) t st' = [] := by
    unfold newRA
    rw [List.mapIdx_eq_nil_iff, List.filter_eq_nil_iff]
    intro i _
    simp [hreq]
  unfold postA
  rw [hpreA, phaseA_fst]
  show st'.queue ++ newRA N.L0 N.L c.params (conRule N c) t st' = _
  rw [hnew, List.append_nil, hstq]

include hact hq hsS hY0 hY hPh in
/-- The shipment invariant along the whole run. -/
theorem inv_ship_all (hs0S : c.s0 ≤ c.S0) (hθ0 : ∀ i, 0 < c.initOffset i ∧ c.initOffset i < 1)
    (d : ℕ → DemandVec n) : ∀ t, act d t →
    InvS N x c act Yp q d t (postA N x c d t)
  | 0, h => absurd h (not_act_zero N x c act hact d)
  | t + 1, h => by
    have hq0 := q_nonneg N x c act Ph q hsS hact hq
    have hIP := (inv_all N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S d (t + 1) h).1
    by_cases h' : act d t
    · have ih := inv_ship_all hs0S hθ0 d t h'
      have hI := (inv_all N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S d t h').1
      have ht := act_time N x c act hact d t h'
      obtain ⟨-, b2, -⟩ := phaseB_step N c act Yp Ph q hq0 hs0S d t ht.1 (postA N x c d t) hI c.params
      have hpost := postA_succ N x c act hact d t h'
      have hmem : ∀ r' ∈ (postA N x c d (t + 1)).queue,
          r' ∈ (phaseB N.L c.params t (postA N x c d t)).1.queue ∨
          r' ∈ newRA N.L0 N.L c.params (conRule N c) (t + 1)
            (receive (applyDemand (phaseB N.L c.params t (postA N x c d t)).1 (d t)) (t + 1)) := by
        intro r' hr'
        rw [hpost, phaseA_fst] at hr'
        exact List.mem_append.1 hr'
      constructor
      · intro r' hr'
        rcases hmem r' hr' with hB | hN
        · rw [b2, List.mem_filter, List.mem_map] at hB
          obtain ⟨⟨r, hr, rfl⟩, -⟩ := hB
          have hk : key r ∈ Lpre N c act Yp q d t := by rw [← hI.keys]; exact List.mem_map_of_mem hr
          unfold Lpre at hk
          rw [List.mem_filter, mem_Lall] at hk
          have hle : r.born ≤ t := hk.1.1
          show _ = if r.born < t + 1 then shx N x c act Yp q d r.born r.ret (t + 1 - 1) else 0
          rw [if_pos (by omega), show t + 1 - 1 = t by omega]
          exact ship_step N x c act Yp Ph q hq0 hs0S d t ht.1 _ hI ih r hr
        · obtain ⟨m1, m2, m3, m4⟩ := newRA_mem _ _ _ _ _ _ r' hN
          rw [m3, m4, if_neg (lt_irrefl _)]
      · intro r' hr' hb
        rcases hmem r' hr' with hB | hN
        · rw [b2, List.mem_filter, List.mem_map] at hB
          obtain ⟨⟨r, hr, rfl⟩, -⟩ := hB
          exact ih.off r hr hb
        · have hoff := newRA_offset _ _ _ _ _ _ r' hN
          have hb' : c.params.batch r'.ret = true := hb
          rw [if_pos hb'] at hoff
          have hrange : 0 < r'.offset ∧ r'.offset < 1 := by
            rw [hoff]; exact conRule_mem N c _ _ _ _ _
          refine ⟨?_, hrange⟩
          have := θx_of_mem N x c act Yp Ph q hq0 d (t + 1) h hIP r' hr'
            (newRA_mem _ _ _ _ _ _ r' hN).2.2.2 hb
          rw [(newRA_mem _ _ _ _ _ _ r' hN).2.2.2]
          exact this.symm
    · have hpre : ∀ t' < t + 1, ¬ act d t' := fun t' ht' ha =>
        h' (act_mono' N x c act hact d (show t' ≤ t by omega) ha)
      have hQ := postA_start_queue N x c act Ph q hsS hact hq d (t + 1) h hpre
      constructor
      · intro r hr
        rw [hQ] at hr
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr
        simp [mkReq]
      · intro r hr hb
        have hr' := hr
        rw [hQ] at hr'
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr'
        refine ⟨?_, (hθ0 i).1, (hθ0 i).2⟩
        exact (θx_of_mem N x c act Yp Ph q (q_nonneg N x c act Ph q hsS hact hq) d (t + 1) h hIP
          _ hr rfl hb).symm

end ship

end OWMR.Eng


/-! Engine lemmas, part 9: offsets, dispatches and orders of the actual run. -/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR


namespace OWMR.Eng

variable {n : ℕ}

lemma crosses_self_false (Q θ : ℝ) (hQ : 0 < Q) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ¬ crossesThreshold Q θ Q Q := by
  rintro (⟨h1, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, -⟩)
  · nlinarith
  · nlinarith
  · exact lt_irrefl _ h1

lemma shippedPath_zero (θ : ℝ) : ∀ k, shippedPath 0 θ (fun _ => 0) k = 0
  | 0 => by simp [shippedPath]
  | k + 1 => by
    simp only [shippedPath]
    rw [shippedPath_zero θ k]
    split_ifs <;> rfl

lemma sum_keys (L : List (ℕ × Fin n)) (hnd : L.Nodup) (t : ℕ) (hle : ∀ k ∈ L, k.1 ≤ t)
    (i : Fin n) (f : ℕ → ℝ) (hz : ∀ s ≤ t, (s, i) ∉ L → f s = 0) :
    ((L.filter (fun k => decide (k.2 = i))).map (fun k => f k.1)).sum
      = ∑ s ∈ Finset.range (t + 1), f s := by
  have hnd' := hnd.filter (fun k => decide (k.2 = i))
  have hnd2 : ((L.filter (fun k => decide (k.2 = i))).map Prod.fst).Nodup :=
    hnd'.map_on fun a ha b hb hab => by
      rw [List.mem_filter] at ha hb
      simp only [decide_eq_true_eq] at ha hb
      exact Prod.ext hab (ha.2.trans hb.2.symm)
  rw [show (fun k : ℕ × Fin n => f k.1) = f ∘ Prod.fst from rfl, ← List.map_map,
    ← List.sum_toFinset f hnd2]
  apply Finset.sum_subset
  · intro s hs
    rw [List.mem_toFinset, List.mem_map] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    rw [List.mem_filter] at hk
    exact Finset.mem_range.2 (by have := hle k hk.1; omega)
  · intro s hs hns
    refine hz s (by have := Finset.mem_range.1 hs; omega) fun hmem => hns ?_
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨(s, i), List.mem_filter.2 ⟨hmem, by simp⟩, rfl⟩

section outputs

variable (N : Network n) (x : InitState n) (c : ConChoice n)
  (act : (ℕ → DemandVec n) → ℕ → Prop) [∀ d, DecidablePred (act d)]
  (Yp : (ℕ → DemandVec n) → ℕ → ℝ) (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
  (hact : ∀ d t, act d t ↔ (N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
  (hY0 : ∀ d, Yp d 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i))
  (hY : ∀ d t, Yp d (t + 1) = (if act d t ∧ Yp d t ≤ c.s0 then c.S0 else Yp d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
  (hPh0 : ∀ d i, Ph d 0 i = c.S i)
  (hPh : ∀ d t i, Ph d (t + 1) i = if act d t then
      (if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i else Ph d t i - ((d t i : ℝ≥0) : ℝ))
      else c.S i)
  (hq : ∀ d t i, q d t i = if act d t then
      (if t = 0 ∨ ¬ act d (t - 1) then
        c.S i - (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
          - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
      else if Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i then
        c.S i - (Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ)) else 0)
    else 0)


include hact hq hsS hY0 hY hPh in
lemma θx_mem (hs0S : c.s0 ≤ c.S0) (hθ0 : ∀ i, 0 < c.initOffset i ∧ c.initOffset i < 1)
    (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) :
    0 < θx N x c act q d s i ∧ θx N x c act q d s i < 1 := by
  unfold θx
  split_ifs with h
  · obtain ⟨hb, ha, hq'⟩ := h
    cases hf : (postA N x c d s).queue.find? (fun r => decide (r.born = s ∧ r.ret = i)) with
    | none => norm_num
    | some r =>
      have hrm := List.mem_of_find?_eq_some hf
      have hrp := List.find?_some hf
      simp only [decide_eq_true_eq] at hrp
      have := (inv_ship_all N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S hθ0 d s ha).off r hrm
        (by rw [hrp.2]; exact hb)
      simp only [Option.elim]
      exact this.2
  · norm_num

/-! ### Dependence on the past -/

include hact in
lemma act_dep (d d' : ℕ → DemandVec n) (t : ℕ) (h : ∀ r < t, d r = d' r) : act d t ↔ act d' t := by
  rw [hact, hact]
  have : ∀ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) = ∑ s ∈ Finset.range t, ((d' s i : ℝ≥0) : ℝ) :=
    fun i => Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.1 hs)]
  simp only [this]

lemma conRun_dep (d d' : ℕ → DemandVec n) : ∀ t, (∀ r < t, d r = d' r) →
    conRun N x c d t = conRun N x c d' t
  | 0, _ => rfl
  | t + 1, h => by
    rw [conRun, conRun, conRun_dep d d' t (fun r hr => h r (by omega)), h t (by omega)]

include hact hPh0 hPh in
lemma Ph_dep (d d' : ℕ → DemandVec n) : ∀ t, (∀ r < t, d r = d' r) → Ph d t = Ph d' t
  | 0, _ => by funext i; rw [hPh0, hPh0]
  | t + 1, h => by
    funext i
    rw [hPh, hPh, Ph_dep d d' t (fun r hr => h r (by omega)), h t (by omega)]
    have := act_dep N x c act hact d d' t (fun r hr => h r (by omega))
    simp only [this]

include hact hPh0 hPh hq in
lemma q_dep (d d' : ℕ → DemandVec n) (t : ℕ) (h : ∀ r < t, d r = d' r) : q d t = q d' t := by
  funext i
  rw [hq, hq]
  have h1 := act_dep N x c act hact d d' t h
  have h2 := act_dep N x c act hact d d' (t - 1) (fun r hr => h r (by omega))
  have h3 : ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) = ∑ s ∈ Finset.range t, ((d' s i : ℝ≥0) : ℝ) :=
    Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.1 hs)]
  have h4 := Ph_dep N x c act Ph hact hPh0 hPh d d' (t - 1) (fun r hr => h r (by omega))
  simp only [h1, h2, h3, h4]
  by_cases ht : act d' t
  · simp only [ht, if_true]
    by_cases ht' : t = 0 ∨ ¬ act d' (t - 1)
    · simp only [ht', if_true]
    · simp only [ht', if_false]
      have ht0 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · exact absurd (Or.inl h0) ht'
        · omega
      rw [h (t - 1) (by omega)]
  · simp only [ht, if_false]

include hact hPh0 hPh hq in
lemma θx_dep (d d' : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (h : ∀ r < s, d r = d' r) :
    θx N x c act q d s i = θx N x c act q d' s i := by
  have e1 := act_dep N x c act hact d d' s h
  have e2 := q_dep N x c act Ph q hact hPh0 hPh hq d d' s h
  have e3 := conRun_dep N x c d d' s h
  unfold θx postA preA
  rw [e2, e3]
  by_cases ha : act d s
  · have ha' := e1.1 ha
    simp only [ha, ha', true_and]
  · have ha' : ¬ act d' s := fun h' => ha (e1.2 h')
    simp only [ha, ha', false_and, and_false, if_false]

/-! ### Orders and dispatches -/

include hact hq hsS hY0 hY hPh in
theorem order_eq (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (t : ℕ) :
    (conPolicy N x c).order t d = q0x c act Yp d t := by
  show (conStep N c t (conRun N x c d t)).2.1 = _
  by_cases h : act d t
  · rw [conStep_act N x c act hact d t h]
    exact (inv_all N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S d t h).2
  · rw [q0x_zero N x c act Yp hact d t h]
    have hpre : ∀ t' < t, ¬ act d t' := fun t' ht' ha =>
      h (act_mono' N x c act hact d (le_of_lt ht') ha)
    rw [conRun_prep N x c act hact d t hpre]
    unfold conStep
    have hr : (receive (prepState N x c d t) t).running = false := rfl
    simp only [hr, Bool.false_eq_true, if_false]
    split_ifs with h1 h2
    · rfl
    · exact absurd ((start_iff N x c act hact d t).1 h2) h
    · rfl

include hact hq hsS hY0 hY hPh in
theorem dispatch_eq (hs0S : c.s0 ≤ c.S0) (hθ0 : ∀ i, 0 < c.initOffset i ∧ c.initOffset i < 1)
    (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) :
    (conPolicy N x c).dispatch t d i = if act d t then
      ∑ s ∈ Finset.range (t + 1), (shx N x c act Yp q d s i t
        - if s < t then shx N x c act Yp q d s i (t - 1) else 0)
    else if t = N.Tpipe - 1 ∧ i = c.sendTo then W0 N x else 0 := by
  show (conStep N c t (conRun N x c d t)).2.2 i = _
  have hq0 := q_nonneg N x c act Ph q hsS hact hq
  by_cases h : act d t
  · rw [if_pos h, conStep_act N x c act hact d t h]
    have ht := act_time N x c act hact d t h
    have hI := (inv_all N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S d t h).1
    have hS := inv_ship_all N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S hθ0 d t h
    obtain ⟨-, -, -, -, -, b6, -, -⟩ :=
      phaseB_step N c act Yp Ph q hq0 hs0S d t ht.1 (postA N x c d t) hI c.params
    show (phaseB N.L c.params t (postA N x c d t)).2 i = _
    rw [b6, pi_sum_apply]
    set f : ℕ → ℝ := fun s => shx N x c act Yp q d s i t
      - if s < t then shx N x c act Yp q d s i (t - 1) else 0 with hf
    have e1 : ((List.filter (fun r => decide (r.ret = i)) (postA N x c d t).queue).map
        (fun r => (serveElem c.params.batch (Vx N c act Yp d t) r (ahx (q d) r.born r.ret)).shipped
          - r.shipped)).sum
        = ((List.filter (fun r => decide (r.ret = i)) (postA N x c d t).queue).map
          (fun r => f r.born)).sum := by
      congr 1
      apply List.map_congr_left
      intro r hr
      rw [List.mem_filter] at hr
      have hri : r.ret = i := of_decide_eq_true hr.2
      rw [ship_step N x c act Yp Ph q hq0 hs0S d t ht.1 _ hI hS r hr.1, hS.ship r hr.1, hri]
    rw [e1]
    have e2 : ((List.filter (fun r => decide (r.ret = i)) (postA N x c d t).queue).map
        (fun r => f r.born)) = (((postA N x c d t).queue.map key).filter
          (fun k => decide (k.2 = i))).map (fun k => f k.1) := by
      rw [List.filter_map, List.map_map]
      rfl
    rw [e2, hI.keys]
    apply sum_keys _ (Lpre_nodup N c act Yp q hq0 d t) t
    · intro k hk
      unfold Lpre at hk
      exact ((mem_Lall _ _ _).1 (List.mem_filter.1 hk).1).1
    · intro s hs hns
      have hθ := θx_mem N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S hθ0 d s i
      by_cases hqs : 0 < q d s i
      · have hmem : (s, i) ∈ Lall (q d) t := (mem_Lall _ _ _).2 ⟨hs, hqs⟩
        have hnp : ¬ (s = t ∨ Vx N c act Yp d (t - 1) < ahx (q d) s i + q d s i) := by
          intro hp
          apply hns
          unfold Lpre
          exact List.mem_filter.2 ⟨hmem, decide_eq_true hp⟩
        push Not at hnp
        have hst : s < t := lt_of_le_of_ne hs hnp.1
        have hVm := Vx_mono N c act Yp hs0S d (show t - 1 ≤ t by omega)
        have hA1 : Ax N c act Yp q d s i (t - 1) = q d s i := by
          unfold Ax
          rw [min_eq_left (by linarith [hnp.2]), max_eq_right hqs.le]
        have hA2 : Ax N c act Yp q d s i t = q d s i := by
          unfold Ax
          rw [min_eq_left (by linarith [hnp.2]), max_eq_right hqs.le]
        simp only [hf, if_pos hst]
        unfold shx
        rw [if_neg (show ¬ t < s by omega), if_neg (show ¬ (t - 1 < s) by omega)]
        by_cases hb : c.batch i = true
        · rw [if_pos hb, if_pos hb]
          obtain ⟨k, hk⟩ : ∃ k, t - s = k + 1 := ⟨t - 1 - s, by omega⟩
          rw [hk, show t - 1 - s = k by omega]
          simp only [shippedPath]
          rw [show s + k = t - 1 by omega, show s + (k + 1) = t by omega, hA1, hA2,
            if_neg (crosses_self_false _ _ hqs hθ.1 hθ.2)]
          ring
        · rw [if_neg hb, if_neg hb, hA1, hA2]; ring
      · have hq0s : q d s i = 0 := le_antisymm (not_lt.1 hqs) (hq0 d s i)
        have hAz : ∀ t', Ax N c act Yp q d s i t' = 0 := fun t' => by
          unfold Ax; rw [hq0s, max_eq_left (min_le_left _ _)]
        have hshz : ∀ t', shx N x c act Yp q d s i t' = 0 := fun t' => by
          unfold shx
          split_ifs with h1 h2
          · rfl
          · rw [hq0s]
            have : (fun k => Ax N c act Yp q d s i (s + k)) = fun _ => 0 := funext fun k => hAz _
            rw [this, shippedPath_zero]
          · exact hAz t'
        simp only [hf, hshz]
        split_ifs <;> ring
  · rw [if_neg h]
    have hpre : ∀ t' < t, ¬ act d t' := fun t' ht' ha =>
      h (act_mono' N x c act hact d (le_of_lt ht') ha)
    rw [conRun_prep N x c act hact d t hpre]
    unfold conStep
    have hr : (receive (prepState N x c d t) t).running = false := rfl
    simp only [hr, Bool.false_eq_true, if_false]
    by_cases hT : t = N.Tpipe - 1
    · rw [if_pos hT]
      have hL0T := L0_le_Tpipe N
      have hWt : (receive (prepState N x c d t) t).Wbar = W0 N x := by
        show prepW N x t + (if t < N.L0 then x.supPipe t else 0) = W0 N x
        unfold prepW W0
        rw [if_pos (by omega), add_assoc]
        congr 1
        rw [← sum_ite_lt_eq x.supPipe N.L0 (t + 1) (by omega), Finset.sum_range_succ]
      show (Pi.single c.sendTo (receive (prepState N x c d t) t).Wbar : Fin n → ℝ) i = _
      rw [hWt]
      by_cases hi : i = c.sendTo
      · subst hi; rw [if_pos ⟨hT, rfl⟩]; simp
      · rw [if_neg (fun h' => hi h'.2), Pi.single_apply, if_neg hi]
    · rw [if_neg hT]
      have hc : ¬ (N.Tpipe - 1 < t ∧ N.Tpipe - 1 + N.L c.sendTo ≤ t ∧
          ∀ i, (receive (prepState N x c d t) t).I i ≤ c.S i) :=
        fun hc => h ((start_iff N x c act hact d t).1 hc)
      rw [if_neg hc, if_neg (fun h' => hT h'.1)]
      rfl

end outputs

end OWMR.Eng


/-! Engine lemmas, part 10: the ideal simulation from a creation state. -/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR


namespace OWMR.Eng

variable {n : ℕ}

/-- The fields of a request that the projected invariant sees. -/
def proj (r : Req n) : ℕ × Fin n × ℝ × ℝ × ℝ := (r.born, r.ret, r.size, r.alloc, r.shipped)

lemma qterm_proj (l l' : List (Req n)) (h : l.map proj = l'.map proj) (i : Fin n) :
    qterm l i (fun r => r.size - r.shipped) = qterm l' i (fun r => r.size - r.shipped) := by
  rw [qterm_eq_map, qterm_eq_map]
  have e : ∀ l : List (Req n), l.map (fun r => if r.ret = i then r.size - r.shipped else 0)
      = (l.map proj).map (fun p => if p.2.1 = i then p.2.2.1 - p.2.2.2.2 else 0) := fun l => by
    rw [List.map_map]; rfl
  rw [e, e, h]

lemma reserve_proj (l l' : List (Req n)) (h : l.map proj = l'.map proj) :
    (l.map (fun r => r.alloc - r.shipped)).sum = (l'.map (fun r => r.alloc - r.shipped)).sum := by
  have e : ∀ l : List (Req n), l.map (fun r => r.alloc - r.shipped)
      = (l.map proj).map (fun p => p.2.2.2.1 - p.2.2.2.2) := fun l => by
    rw [List.map_map]; rfl
  rw [e, e, h]

section ideal

variable (N : Network n) (c : ConChoice n) (act : (ℕ → DemandVec n) → ℕ → Prop)
  [∀ d, DecidablePred (act d)] (Yp : (ℕ → DemandVec n) → ℕ → ℝ)
  (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ) (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)

/-- The projected invariant only sees the projected queue. -/
lemma InvP_congr (d : ℕ → DemandVec n) (t : ℕ) (Z Z' : EngState n)
    (hW : Z'.Wbar = Z.Wbar) (hsup : Z'.supPipe = Z.supPipe) (hI : Z'.I = Z.I)
    (hR : Z'.retPipe = Z.retPipe) (hn : Z'.nOrd = Z.nOrd)
    (hq : Z'.queue.map proj = Z.queue.map proj) (h : InvP N c act Yp Ph q d t Z) :
    InvP N c act Yp Ph q d t Z' := by
  have hkey : Z'.queue.map key = Z.queue.map key := by
    have e : ∀ l : List (Req n), l.map key = (l.map proj).map (fun p => (p.1, p.2.1)) :=
      fun l => by rw [List.map_map]; rfl
    rw [e, e, hq]
  have hmem : ∀ r' ∈ Z'.queue, ∃ r ∈ Z.queue, proj r = proj r' := by
    intro r' hr'
    have : proj r' ∈ Z.queue.map proj := by rw [← hq]; exact List.mem_map_of_mem hr'
    obtain ⟨r, hr, e⟩ := List.mem_map.1 this
    exact ⟨r, hr, e⟩
  have hphys : ∀ i, physPos N.L Z' t i = physPos N.L Z t i := fun i => by
    unfold physPos inTransit; rw [hI, hR]
  constructor
  · rw [hW]; exact h.wbar
  · intro r hr; rw [hsup]; exact h.sup r hr
  · rw [hkey]; exact h.keys
  · intro r' hr'
    obtain ⟨r, hr, e⟩ := hmem r' hr'
    simp only [proj, Prod.mk.injEq] at e
    obtain ⟨e1, e2, e3, e4, e5⟩ := e
    rw [← e1, ← e2, ← e3, ← e4, ← e5]
    exact h.elems r hr
  · intro i
    have := h.phat i
    rw [phat_eq] at this ⊢
    rw [hphys, qterm_proj _ _ hq]
    exact this
  · intro i r hr; rw [hR]; exact h.ret i r hr
  · rw [hn]; exact h.nord
  · have := h.pos
    unfold posE at this ⊢
    rw [sum_reserve] at this ⊢
    rw [reserve_proj _ _ hq]
    have e2 : supInTransit N.L0 Z' t = supInTransit N.L0 Z t := by
      unfold supInTransit; rw [hsup]
    rw [hW, e2]
    simp only [hphys]
    exact this

end ideal

section dep

variable (N : Network n) (x : InitState n) (c : ConChoice n)
  (act : (ℕ → DemandVec n) → ℕ → Prop) [∀ d, DecidablePred (act d)]
  (Yp : (ℕ → DemandVec n) → ℕ → ℝ) (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
  (hact : ∀ d t, act d t ↔ (N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
  (hY0 : ∀ d, Yp d 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i))
  (hY : ∀ d t, Yp d (t + 1) = (if act d t ∧ Yp d t ≤ c.s0 then c.S0 else Yp d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
  (hPh0 : ∀ d i, Ph d 0 i = c.S i)
  (hPh : ∀ d t i, Ph d (t + 1) i = if act d t then
      (if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i else Ph d t i - ((d t i : ℝ≥0) : ℝ))
      else c.S i)
  (hq : ∀ d t i, q d t i = if act d t then
      (if t = 0 ∨ ¬ act d (t - 1) then
        c.S i - (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
          - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
      else if Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i then
        c.S i - (Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ)) else 0)
    else 0)


include hact hY0 hY in
lemma Yp_dep (d d' : ℕ → DemandVec n) : ∀ t, (∀ r < t, d r = d' r) → Yp d t = Yp d' t
  | 0, _ => by rw [hY0, hY0]
  | t + 1, h => by
    rw [hY, hY, Yp_dep d d' t (fun r hr => h r (by omega)), h t (by omega)]
    have := act_dep N x c act hact d d' t (fun r hr => h r (by omega))
    simp only [this]

include hact hY0 hY in
lemma q0x_dep (d d' : ℕ → DemandVec n) (t : ℕ) (h : ∀ r < t, d r = d' r) :
    q0x c act Yp d t = q0x c act Yp d' t := by
  unfold q0x
  rw [Yp_dep N x c act Yp hact hY0 hY d d' t h]
  have := act_dep N x c act hact d d' t h
  simp only [this]

include hact hY0 hY in
lemma Vx_dep (d d' : ℕ → DemandVec n) (t : ℕ) (h : ∀ r < t, d r = d' r) :
    Vx N c act Yp d t = Vx N c act Yp d' t :=
  Finset.sum_congr rfl fun r hr => q0x_dep N x c act Yp hact hY0 hY d d' r (fun r' hr' => h r' (by
    simp only [Finset.mem_range] at hr; omega))

include hact hPh0 hPh hq in
lemma Pq_dep (d d' : ℕ → DemandVec n) (t : ℕ) (h : ∀ r < t, d r = d' r) :
    Pq (q d) t = Pq (q d') t :=
  Finset.sum_congr rfl fun r hr => by
    rw [q_dep N x c act Ph q hact hPh0 hPh hq d d' r (fun r' hr' => h r' (by
      simp only [Finset.mem_range] at hr; omega))]

include hact hPh0 hPh hq in
lemma ahx_dep (d d' : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (h : ∀ r < s, d r = d' r) :
    ahx (q d) s i = ahx (q d') s i := by
  unfold ahx
  rw [Pq_dep N x c act Ph q hact hPh0 hPh hq d d' s h,
    q_dep N x c act Ph q hact hPh0 hPh hq d d' s h]

include hact hPh0 hPh hq in
lemma Lall_dep (d d' : ℕ → DemandVec n) (t : ℕ) (h : ∀ r < t, d r = d' r) :
    Lall (q d) t = Lall (q d') t := by
  unfold Lall
  apply List.flatMap_congr
  intro r hr
  unfold perL
  rw [q_dep N x c act Ph q hact hPh0 hPh hq d d' r (fun r' hr' => h r' (by
    simp only [List.mem_range] at hr; omega))]

include hact hY0 hY hPh0 hPh hq in
lemma InvP_dep (d d' : ℕ → DemandVec n) (t : ℕ) (ht : 1 ≤ t) (h : ∀ r < t, d r = d' r)
    (Z : EngState n) (hI : InvP N c act Yp Ph q d t Z) : InvP N c act Yp Ph q d' t Z := by
  have hV1 := Vx_dep N x c act Yp hact hY0 hY d d' (t - 1) (fun r hr => h r (by omega))
  have hV := Vx_dep N x c act Yp hact hY0 hY d d' t h
  have hPq := Pq_dep N x c act Ph q hact hPh0 hPh hq d d' t h
  have hqd : ∀ r ≤ t, q d r = q d' r := fun r hr =>
    q_dep N x c act Ph q hact hPh0 hPh hq d d' r (fun r' hr' => h r' (by omega))
  have hah : ∀ r ≤ t, ∀ i, ahx (q d) r i = ahx (q d') r i := fun r hr i =>
    ahx_dep N x c act Ph q hact hPh0 hPh hq d d' r i (fun r' hr' => h r' (by omega))
  have hLall := Lall_dep N x c act Ph q hact hPh0 hPh hq d d' t h
  have hLpre : Lpre N c act Yp q d t = Lpre N c act Yp q d' t := by
    unfold Lpre
    rw [hLall, hV1]
    apply List.filter_congr
    intro k hk
    rw [mem_Lall] at hk
    rw [hah k.1 hk.1 k.2, hqd k.1 hk.1]
  have hborn : ∀ r ∈ Z.queue, r.born ≤ t := fun r hr => by
    have hk : key r ∈ Lpre N c act Yp q d t := by rw [← hI.keys]; exact List.mem_map_of_mem hr
    unfold Lpre at hk
    exact ((mem_Lall _ _ _).1 (List.mem_filter.1 hk).1).1
  constructor
  · rw [hI.wbar, hV1, hV, hPq]
  · intro r hr
    rw [hI.sup r hr]
    split_ifs with h1
    · exact q0x_dep N x c act Yp hact hY0 hY d d' _ (fun r' hr' => h r' (by omega))
    · rfl
  · rw [hI.keys, hLpre]
  · intro r hr
    obtain ⟨e1, e2, e3, e4⟩ := hI.elems r hr
    rw [hqd _ (hborn r hr), hV1, hPq, hah _ (hborn r hr)] at *
    exact ⟨e1, e2, e3, e4⟩
  · intro i
    rw [hI.phat i, Ph_dep N x c act Ph hact hPh0 hPh d d' t h]
  · exact hI.ret
  · rw [hI.nord]
    unfold nOx
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r ≤ t := by simp only [Finset.mem_range] at hr; omega
    rw [hqd r hr']
    have := act_dep N x c act hact d d' (r - 1) (fun r' hr'' => h r' (by omega))
    simp only [this]
  · rw [hI.pos]
    unfold Ypost
    rw [Yp_dep N x c act Yp hact hY0 hY d d' t h]

end dep

end OWMR.Eng


/-! Engine lemmas, part 11: identification of the ideal simulation used by the offset rule. -/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR


namespace OWMR.Eng

variable {n : ℕ}

/-- The demand path that follows `d` before `s` and the fresh block `ds` from `s` on. -/
def splice (L0 : ℕ) (d : ℕ → DemandVec n) (s : ℕ) (ds : Fin L0 → DemandVec n) : ℕ → DemandVec n :=
  fun r => if r < s then d r else padHist L0 ds (r - s)

section ident

variable (N : Network n) (x : InitState n) (c : ConChoice n)
  (act : (ℕ → DemandVec n) → ℕ → Prop) [∀ d, DecidablePred (act d)]
  (Yp : (ℕ → DemandVec n) → ℕ → ℝ) (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
  (hact : ∀ d t, act d t ↔ (N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
  (hY0 : ∀ d, Yp d 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i))
  (hY : ∀ d t, Yp d (t + 1) = (if act d t ∧ Yp d t ≤ c.s0 then c.S0 else Yp d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
  (hPh0 : ∀ d i, Ph d 0 i = c.S i)
  (hPh : ∀ d t i, Ph d (t + 1) i = if act d t then
      (if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i else Ph d t i - ((d t i : ℝ≥0) : ℝ))
      else c.S i)
  (hq : ∀ d t i, q d t i = if act d t then
      (if t = 0 ∨ ¬ act d (t - 1) then
        c.S i - (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
          - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
      else if Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i then
        c.S i - (Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ)) else 0)
    else 0)


include hact hY0 hY in
lemma Vx_dep_le (d d' : ℕ → DemandVec n) (s t : ℕ) (h : ∀ r < s, d r = d' r)
    (hle : t + 1 - N.L0 ≤ s + 1) : Vx N c act Yp d t = Vx N c act Yp d' t :=
  Finset.sum_congr rfl fun r hr => q0x_dep N x c act Yp hact hY0 hY d d' r (fun r' hr' => h r' (by
    simp only [Finset.mem_range] at hr; omega))

include hact hq hsS hY0 hY hPh0 hPh in
/-- The ideal simulation from the creation state of request `(s,i)` follows the explicit run. -/
theorem ideal_inv (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (s : ℕ) (hs : 1 ≤ s)
    (ha : act d s) (σ : EngState n) (hσ : InvP N c act Yp Ph q d s σ)
    (ds : Fin N.L0 → DemandVec n) :
    ∀ k, InvP N c act Yp Ph q (splice N.L0 d s ds) (s + k)
      (idealA N c.params σ s (padHist N.L0 ds) k)
  | 0 => by
    simp only [idealA, add_zero]
    exact InvP_dep N x c act Yp Ph q hact hY0 hY hPh0 hPh hq d (splice N.L0 d s ds) s hs
      (fun r hr => by simp [splice, hr]) σ hσ
  | k + 1 => by
    have ih := ideal_inv hs0S d s hs ha σ hσ ds k
    have had : act (splice N.L0 d s ds) (s + k) :=
      act_mono' N x c act hact _ (show s ≤ s + k by omega)
        ((act_dep N x c act hact d (splice N.L0 d s ds) s (fun r hr => by simp [splice, hr])).1 ha)
    have hgen := step_generic N c act Yp Ph q (q_nonneg N x c act Ph q hsS hact hq) hs0S hY hPh
      (fun d t i ha => q_ord N x c act Ph q hact hq d t ha i)
      (fun d t ha => act_mono N x c act hact d t ha)
      (fun d t ha => (act_time N x c act hact d t ha).2.1)
      (splice N.L0 d s ds) (s + k) (by omega) had _ ih
      { c.params with batch := fun _ => false } { c.params with batch := fun _ => false }
      ⟨rfl, rfl, rfl, rfl, rfl⟩ (fun _ _ _ _ _ => 0)
    have hds : splice N.L0 d s ds (s + k) = padHist N.L0 ds k := by
      simp only [splice, show ¬ (s + k < s) by omega, if_false, Nat.add_sub_cancel_left]
    rw [hds] at hgen
    exact hgen.1

include hact hq hsS hY0 hY hPh0 hPh in
/-- The offset rule is applied to a creation state whose ideal simulation follows the explicit run:
the allocations of the new request and the total depletion over its lifetime. -/
theorem ident (hs0S : c.s0 ≤ c.S0) (hθ0 : ∀ i, 0 < c.initOffset i ∧ c.initOffset i < 1)
    (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (hs : 0 < s) (ha : act d (s - 1))
    (hqs : 0 < q d s i) (hb : c.batch i = true) :
    ∃ σ : EngState n,
      θx N x c act q d s i = conRule N c σ s (nOx act q d (s - 1)
        + ((List.finRange n).filter (fun j => decide (0 < q d s j))).idxOf i + 1) i (q d s i) ∧
      ∀ (ds : Fin N.L0 → DemandVec n) (k : ℕ), k ≤ N.L0 →
        idealAlloc N c.params σ s i (q d s i) (padHist N.L0 ds) k = Ax N c act Yp q d s i (s + k) ∧
        idealDepletion N c.params σ s (padHist N.L0 ds) k
          = ∑ j, (c.S j - Ph (splice N.L0 d s ds) (s + k) j) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [add_tsub_cancel_right] at ha ⊢
  have hq0 := q_nonneg N x c act Ph q hsS hact hq
  have has := act_mono N x c act hact d t ha
  have ht := act_time N x c act hact d t ha
  have hI := (inv_all N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S d t ha).1
  have hI1 := (inv_all N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S d (t + 1) has).1
  obtain ⟨-, b2, -, b4, b5, -, -, b8⟩ :=
    phaseB_step N c act Yp Ph q hq0 hs0S d t ht.1 (postA N x c d t) hI c.params
  set B := (phaseB N.L c.params t (postA N x c d t)).1 with hB
  set R := receive (applyDemand B (d t)) (t + 1) with hR
  have hpost : postA N x c d (t + 1) = (phaseA N.L0 N.L c.params (conRule N c) (t + 1) R).1 :=
    postA_succ N x c act hact d t ha
  have hphatR : ∀ j, phat N.L R (t + 1) j = Ph d t j - ((d t j : ℝ≥0) : ℝ) := fun j => by
    have h0 : (applyDemand B (d t)).retPipe j (t + 1 + N.L j) = 0 := b5 j _ (by omega)
    rw [hR, phat_receive N.L (applyDemand B (d t)) t j h0, phat_applyDemand, b8, hI.phat]
  have hreq : ∀ j, reqSize N.L c.params R (t + 1) j = q d (t + 1) j := fun j => by
    unfold reqSize
    rw [hphatR, q_ord N x c act Ph q hact hq d t ha j]
    rfl
  have hrs : (List.finRange n).filter (fun j => decide (0 < reqSize N.L c.params R (t + 1) j))
      = (List.finRange n).filter (fun j => decide (0 < q d (t + 1) j)) :=
    List.filter_congr fun j _ => by rw [hreq]
  have hnord : R.nOrd = nOx act q d t := by
    rw [hR]; simp only [receive_nOrd, applyDemand_nOrd]; rw [b4, hI.nord]
  -- the new request of retailer `i`
  have hkey : (t + 1, i) ∈ Lpre N c act Yp q d (t + 1) := by
    unfold Lpre
    exact List.mem_filter.2 ⟨(mem_Lall _ _ _).2 ⟨le_rfl, hqs⟩, by simp⟩
  rw [← hI1.keys] at hkey
  obtain ⟨r, hr, hrk⟩ := List.mem_map.1 hkey
  simp only [key, Prod.mk.injEq] at hrk
  obtain ⟨hrb, hri⟩ := hrk
  have hrN : r ∈ newRA N.L0 N.L c.params (conRule N c) (t + 1) R := by
    have hr' := hr
    rw [hpost, phaseA_fst] at hr'
    rcases List.mem_append.1 hr' with h1 | h1
    · exfalso
      have hk := phaseB_keys N c act Yp Ph q hq0 hs0S d t ht.1 (postA N x c d t) hI c.params
      have : key r ∈ (Lall (q d) t).filter (fun k =>
          decide (Vx N c act Yp d t < ahx (q d) k.1 k.2 + q d k.1 k.2)) := by
        rw [← hk]; exact List.mem_map_of_mem h1
      have := ((mem_Lall _ _ _).1 (List.mem_filter.1 this).1).1
      simp only [key] at this
      omega
    · exact h1
  have hθ := θx_of_mem N x c act Yp Ph q hq0 d (t + 1) has hI1 r hr hrb (by rw [hri]; exact hb)
  have hoff := newRA_offset _ _ _ _ _ _ r hrN
  rw [show c.params.batch r.ret = true by rw [hri]; exact hb, if_pos rfl] at hoff
  set σ : EngState n :=
    { R with
      Wbar := if N.L0 = 0 then R.Wbar + (phaseA N.L0 N.L c.params (conRule N c) (t + 1) R).2
        else R.Wbar
      supPipe := if N.L0 = 0 then R.supPipe
        else Function.update R.supPipe (t + 1 + N.L0)
          (R.supPipe (t + 1 + N.L0) + (phaseA N.L0 N.L c.params (conRule N c) (t + 1) R).2)
      queue := R.queue ++ ((List.finRange n).filter
        (fun i => decide (0 < reqSize N.L c.params R (t + 1) i))).map (fun i =>
          ({ ret := i, size := reqSize N.L c.params R (t + 1) i, alloc := 0, shipped := 0,
             offset := 0, born := t + 1 } : Req n))
      nOrd := R.nOrd + ((List.finRange n).filter
        (fun i => decide (0 < reqSize N.L c.params R (t + 1) i))).length } with hσdef
  refine ⟨σ, ?_, ?_⟩
  · rw [← hri, hθ, hoff, hnord, hrs, hreq]
  · intro ds k hk
    -- the creation state satisfies the projected invariant
    have hσ : InvP N c act Yp Ph q d (t + 1) σ := by
      have e1 : σ.Wbar = (postA N x c d (t + 1)).Wbar := by rw [hpost, phaseA_fst]
      have e2 : σ.supPipe = (postA N x c d (t + 1)).supPipe := by rw [hpost, phaseA_fst]
      have e3 : σ.I = (postA N x c d (t + 1)).I := by rw [hpost, phaseA_fst]
      have e4 : σ.retPipe = (postA N x c d (t + 1)).retPipe := by rw [hpost, phaseA_fst]
      have e5 : σ.nOrd = (postA N x c d (t + 1)).nOrd := by rw [hpost, phaseA_fst]
      refine InvP_congr N c act Yp Ph q d (t + 1) (postA N x c d (t + 1)) σ e1 e2 e3 e4 e5 ?_ hI1
      rw [hpost, phaseA_fst]
      show (R.queue ++ _).map proj = (R.queue ++ newRA N.L0 N.L c.params (conRule N c) (t + 1) R).map proj
      rw [List.map_append, List.map_append]
      congr 1
      unfold newRA
      rw [map_mapIdx_const proj (fun j => (t + 1, j, reqSize N.L c.params R (t + 1) j, 0, 0)) _ _
        (fun _ _ => rfl), List.map_map]
      rfl
    have hinv := ideal_inv N x c act Yp Ph q hsS hact hY0 hY hPh0 hPh hq hs0S d (t + 1) (by omega)
      has σ hσ ds k
    set d' := splice N.L0 d (t + 1) ds with hd'
    have hagree : ∀ r < t + 1, d r = d' r := fun r hr => by simp [hd', splice, hr]
    have hqq : q d (t + 1) = q d' (t + 1) := q_dep N x c act Ph q hact hPh0 hPh hq d d' (t + 1) hagree
    constructor
    · -- allocations of the new request
      unfold idealAlloc
      set P' : EngParams n := { c.params with batch := fun _ => false } with hP'
      set Zk := idealA N c.params σ (t + 1) (padHist N.L0 ds) k with hZk
      obtain ⟨-, hb2, -⟩ := phaseB_step N c act Yp Ph q hq0 hs0S d' (t + 1 + k) (by omega) Zk hinv P'
      have hkk := phaseB_keys N c act Yp Ph q hq0 hs0S d' (t + 1 + k) (by omega) Zk hinv P'
      have hAx : Ax N c act Yp q d (t + 1) i (t + 1 + k) = Ax N c act Yp q d' (t + 1) i (t + 1 + k) := by
        unfold Ax
        rw [hqq, ahx_dep N x c act Ph q hact hPh0 hPh hq d d' (t + 1) i hagree,
          Vx_dep_le N x c act Yp hact hY0 hY d d' (t + 1) (t + 1 + k) hagree (by omega)]
      rw [hAx]
      by_cases hin : (t + 1, i) ∈ (phaseB N.L P' (t + 1 + k) Zk).1.queue.map key
      · obtain ⟨r', hr', hrk'⟩ := List.mem_map.1 hin
        have hnd : ((phaseB N.L P' (t + 1 + k) Zk).1.queue.map key).Nodup := by
          rw [hkk]; exact (Lall_nodup (q d') (hq0 d') _).filter _
        have hf := find_key _ hnd r' hr'
        simp only [key, Prod.mk.injEq] at hrk'
        rw [hrk'.1, hrk'.2] at hf
        rw [hf]
        dsimp only
        have hr'' := hr'
        rw [hb2, List.mem_filter, List.mem_map] at hr''
        obtain ⟨⟨r0, hr0, hr0e⟩, -⟩ := hr''
        have hsz := (hinv.elems r0 hr0).1
        have hkey0 : r0.born = t + 1 ∧ r0.ret = i := by
          rw [← hr0e] at hrk'; exact hrk'
        rw [← hr0e]
        show max 0 (min r0.size (Vx N c act Yp d' (t + 1 + k) - ahx (q d') r0.born r0.ret)) = _
        rw [hsz, hkey0.1, hkey0.2]
        rfl
      · have hnone : (phaseB N.L P' (t + 1 + k) Zk).1.queue.find?
            (fun r => decide (r.born = t + 1 ∧ r.ret = i)) = none := by
          rw [List.find?_eq_none]
          intro r hr hp
          apply hin
          simp only [decide_eq_true_eq] at hp
          exact List.mem_map.2 ⟨r, hr, by simp [key, hp.1, hp.2]⟩
        rw [hnone]
        dsimp only
        rw [hkk] at hin
        have hmem : (t + 1, i) ∈ Lall (q d') (t + 1 + k) :=
          (mem_Lall _ _ _).2 ⟨by simp, by rw [← hqq]; exact hqs⟩
        have hnot : ¬ Vx N c act Yp d' (t + 1 + k) < ahx (q d') (t + 1) i + q d' (t + 1) i := by
          intro hlt
          exact hin (List.mem_filter.2 ⟨hmem, by simp [hlt]⟩)
        rw [not_lt] at hnot
        unfold Ax
        rw [← hqq, min_eq_left (by rw [hqq]; linarith), max_eq_right hqs.le]
    · -- the total depletion
      unfold idealDepletion
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hinv.phat j]
      rfl

end ident

end OWMR.Eng


open MeasureTheory
open scoped ENNReal NNReal
open OWMR OWMR.Eng

theorem solution {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)
    (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
    (hθ0 : ∀ i, 0 < c.initOffset i ∧ c.initOffset i < 1)
    (act : (ℕ → DemandVec n) → ℕ → Prop) [∀ d, DecidablePred (act d)]
    (hact : ∀ d t, act d t ↔ (N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
    (Yp : (ℕ → DemandVec n) → ℕ → ℝ)
    (hY0 : ∀ d, Yp d 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i))
    (hY : ∀ d t, Yp d (t + 1) = (if act d t ∧ Yp d t ≤ c.s0 then c.S0 else Yp d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
    (Ph : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
    (hPh0 : ∀ d i, Ph d 0 i = c.S i)
    (hPh : ∀ d t i, Ph d (t + 1) i = if act d t then
      (if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i else Ph d t i - ((d t i : ℝ≥0) : ℝ))
      else c.S i)
    (q : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
    (hq : ∀ d t i, q d t i = if act d t then
      (if t = 0 ∨ ¬ act d (t - 1) then
        c.S i - (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
          - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
      else if Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i then
        c.S i - (Ph d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ)) else 0)
      else 0)
    (A : (ℕ → DemandVec n) → ℕ → Fin n → ℕ → ℝ)
    (hA : ∀ d s i t, A d s i t = max 0 (min (q d s i)
      (∑ r ∈ Finset.range (t + 1 - N.L0), (if act d r ∧ Yp d r ≤ c.s0 then c.S0 - Yp d r else 0)
        - (∑ r ∈ Finset.range s, ∑ j, q d r j + ∑ j ∈ Finset.univ.filter (· < i), q d s j)))) :
    ∃ θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ,
      (∀ d s i, 0 < θ d s i ∧ θ d s i < 1) ∧
      (∀ d d' s, (∀ r < s, d r = d' r) → ∀ i, θ d s i = θ d' s i) ∧
      (∀ d t, (conPolicy N x c).order t d
        = if act d t ∧ Yp d t ≤ c.s0 then c.S0 - Yp d t else 0) ∧
      (∀ d t i, (conPolicy N x c).dispatch t d i = if act d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q d s i) (θ d s i) (fun k => A d s i (s + k)) (t - s)
              else A d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q d s i) (θ d s i) (fun k => A d s i (s + k)) (t - 1 - s)
              else A d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0) ∧
      (∀ d s i, 0 < s → act d (s - 1) → 0 < q d s i → c.batch i = true →
        ∃ σ : EngState n,
          θ d s i = conRule N c σ s (∑ r ∈ Finset.range s,
              (if 0 < r ∧ act d (r - 1) then
                ((List.finRange n).filter (fun j => decide (0 < q d r j))).length else 0)
            + ((List.finRange n).filter (fun j => decide (0 < q d s j))).idxOf i + 1) i (q d s i) ∧
          ∀ (ds : Fin N.L0 → DemandVec n) (k : ℕ), k ≤ N.L0 →
            idealAlloc N c.params σ s i (q d s i) (padHist N.L0 ds) k = A d s i (s + k) ∧
            idealDepletion N c.params σ s (padHist N.L0 ds) k
              = ∑ j, (c.S j - Ph (fun r => if r < s then d r else padHist N.L0 ds (r - s)) (s + k) j)) := by
  have hAx : ∀ d s i t, Ax N c act Yp q d s i t = A d s i t := fun d s i t => by
    rw [hA]; rfl
  refine ⟨θx N x c act q, fun d s i => θx_mem N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S hθ0 d s i,
    fun d d' s h i => θx_dep N x c act Ph q hact hPh0 hPh hq d d' s i h, fun d t => ?_,
    fun d t i => ?_, fun d s i hs ha hqs hb => ?_⟩
  · rw [order_eq N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S d t]
    rfl
  · have hshx : ∀ s t, s ≤ t → shx N x c act Yp q d s i t = if c.batch i then
        shippedPath (q d s i) (θx N x c act q d s i) (fun k => A d s i (s + k)) (t - s)
        else A d s i t := fun s t hst => by
      unfold shx
      rw [if_neg (show ¬ t < s by omega)]
      simp only [hAx]
    rw [dispatch_eq N x c act Yp Ph q hsS hact hY0 hY hPh hq hs0S hθ0 d t i]
    by_cases h1 : act d t
    · rw [if_pos h1, if_pos h1]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs' : s ≤ t := by simp only [Finset.mem_range] at hs; omega
      rw [hshx s t hs']
      by_cases h2 : s < t
      · rw [if_pos h2, if_pos h2, hshx s (t - 1) (by omega)]
      · rw [if_neg h2, if_neg h2]
    · rw [if_neg h1, if_neg h1]
      rfl
  · obtain ⟨σ, h1, h2⟩ := ident N x c act Yp Ph q hsS hact hY0 hY hPh0 hPh hq hs0S hθ0 d s i hs ha
      hqs hb
    refine ⟨σ, ?_, fun ds k hk => ?_⟩
    · rw [h1]
      unfold nOx
      rw [show s - 1 + 1 = s by omega]
    · obtain ⟨e1, e2⟩ := h2 ds k hk
      exact ⟨by rw [e1, hAx], e2⟩
