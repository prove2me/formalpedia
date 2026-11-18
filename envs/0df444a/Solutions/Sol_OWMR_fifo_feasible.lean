-- Prove2me | solution 1 for OWMR.fifo_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:52.198536+00:00
-- url     : https://prove2.me/submissions/599ff1ba-07d0-4ae8-9246-fcbc0935dc7d

import Definitions.Def_owmr_fifo_policy

/-!
FIFO engine invariants (Section 5.1, Lemma 7): along every demand path, the order of `π_FIFO`
follows the supplier `(s₀,S₀)` rule on the echelon position `Yp`, the warehouse stock is
nonnegative, each retailer's request position `P̂ = P + Δ` (physical position plus unallocated
requests) follows its `(sᵢ,Sᵢ)` rule from `Sᵢ` at the start, the warehouse stock and the
unallocated quantities are never both positive, and the dispatch setups are charged to request
setups plus `K_max` per initial request, per prescribed supplier receipt and per supplier order
(at most one continuation per positive supplier receipt, since only the head of the FIFO queue
can be partly filled).
-/

open scoped ENNReal NNReal
open OWMR

variable {n : ℕ}

/-- A request whose shipments equal its allocation, with `0 ≤ alloc ≤ size`. -/
private def Good (r : Req n) : Prop := r.shipped = r.alloc ∧ 0 ≤ r.alloc ∧ r.alloc ≤ r.size

/-- Unallocated quantity of retailer `i` in a list of requests. -/
private noncomputable def uL (l : List (Req n)) (i : Fin n) : ℝ :=
  ((l.filter (fun r => r.ret = i)).map (fun r => r.size - r.alloc)).sum

/-- Setup charge carried by the requests with no allocation yet. -/
private noncomputable def zK (K : Fin n → ℝ) (l : List (Req n)) : ℝ :=
  ((l.filter (fun r => r.alloc = 0)).map (fun r => K r.ret)).sum

private noncomputable def flt (l : List (Req n)) : List (Req n) :=
  l.filter (fun r => r.shipped < r.size)

private lemma sum_map_filter_eq {β : Type} (l : List β) (q : β → Bool) (h : β → ℝ) :
    ((l.filter q).map h).sum = (l.map (fun j => if q j then h j else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hq : q a <;> simp [hq, ih]

/-- A request after receiving allocation `a` and shipping it. -/
private def upd (r : Req n) (a : ℝ) : Req n := { r with alloc := r.alloc + a, shipped := r.alloc + a }

@[simp] private lemma upd_ret (r : Req n) (a : ℝ) : (upd r a).ret = r.ret := rfl
@[simp] private lemma upd_size (r : Req n) (a : ℝ) : (upd r a).size = r.size := rfl
@[simp] private lemma upd_alloc (r : Req n) (a : ℝ) : (upd r a).alloc = r.alloc + a := rfl
@[simp] private lemma upd_shipped (r : Req n) (a : ℝ) : (upd r a).shipped = r.alloc + a := rfl

private lemma serve_nil (w : ℝ) : serve (n := n) (fun _ => false) [] w = ([], w, 0) := rfl

private lemma serve_cons (r : Req n) (rs : List (Req n)) (w : ℝ) :
    serve (fun _ => false) (r :: rs) w =
      (upd r (min (r.size - r.alloc) w)
          :: (serve (fun _ => false) rs (w - min (r.size - r.alloc) w)).1,
        (serve (fun _ => false) rs (w - min (r.size - r.alloc) w)).2.1,
        (serve (fun _ => false) rs (w - min (r.size - r.alloc) w)).2.2
          + Pi.single r.ret (r.alloc + min (r.size - r.alloc) w - r.shipped)) := by
  simp only [serve, true_or, if_true, upd]
  congr 2
  ring_nf

private lemma serve_fst_length (l : List (Req n)) (w : ℝ) :
    (serve (fun _ => false) l w).1.length = l.length := by
  induction l generalizing w with
  | nil => rfl
  | cons r rs ih => simp [serve_cons, ih]

/-- Remaining stock is nonnegative. -/
private lemma serve_w_nonneg (l : List (Req n)) (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ (serve (fun _ => false) l w).2.1 := by
  induction l generalizing w with
  | nil => simpa [serve_nil] using hw
  | cons r rs ih =>
    rw [serve_cons]
    exact ih _ (by linarith [min_le_right (r.size - r.alloc) w])

/-- Goodness is preserved. -/
private lemma serve_good (l : List (Req n)) (w : ℝ) (hw : 0 ≤ w) (hl : ∀ r ∈ l, Good r) :
    ∀ r ∈ (serve (fun _ => false) l w).1, Good r := by
  induction l generalizing w with
  | nil => simp [serve_nil]
  | cons r rs ih =>
    rw [serve_cons]
    have hr := hl r (by simp)
    have ha0 : 0 ≤ min (r.size - r.alloc) w := le_min (by linarith [hr.2.2]) hw
    intro r' hr'
    rcases List.mem_cons.1 hr' with h | h
    · subst h
      refine ⟨rfl, by simp only [upd]; linarith [hr.2.1], ?_⟩
      simp only [upd]
      linarith [min_le_left (r.size - r.alloc) w]
    · exact ih _ (by linarith [min_le_right (r.size - r.alloc) w])
        (fun r'' h'' => hl r'' (by simp [h''])) r' h

/-- Conservation: remaining stock plus total shipments equals the initial stock. -/
private lemma serve_conserve (l : List (Req n)) (w : ℝ) (hl : ∀ r ∈ l, Good r) :
    (serve (fun _ => false) l w).2.1 + ∑ i, (serve (fun _ => false) l w).2.2 i = w := by
  induction l generalizing w with
  | nil => simp [serve_nil]
  | cons r rs ih =>
    rw [serve_cons]
    have hr := hl r (by simp)
    have ih' := ih (w - min (r.size - r.alloc) w) (fun r'' h'' => hl r'' (by simp [h'']))
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    simp only [Finset.mem_univ, if_true]
    rw [hr.1]
    linarith

/-- Shipments are nonnegative. -/
private lemma serve_ship_nonneg (l : List (Req n)) (w : ℝ) (hw : 0 ≤ w) (hl : ∀ r ∈ l, Good r)
    (i : Fin n) : 0 ≤ (serve (fun _ => false) l w).2.2 i := by
  induction l generalizing w with
  | nil => simp [serve_nil]
  | cons r rs ih =>
    rw [serve_cons]
    have hr := hl r (by simp)
    have ha0 : 0 ≤ min (r.size - r.alloc) w := le_min (by linarith [hr.2.2]) hw
    have h1 := ih (w - min (r.size - r.alloc) w) (by linarith [min_le_right (r.size - r.alloc) w])
      (fun r'' h'' => hl r'' (by simp [h'']))
    simp only [Pi.add_apply]
    rw [hr.1]
    have : 0 ≤ Pi.single (M := fun _ => ℝ) r.ret (r.alloc + min (r.size - r.alloc) w - r.alloc) i := by
      by_cases h : i = r.ret
      · rw [h, Pi.single_eq_same]; linarith
      · rw [Pi.single_eq_of_ne h]
    linarith

/-- Per-retailer accounting: unallocated quantity falls by the shipments. -/
private lemma serve_uL (l : List (Req n)) (w : ℝ) (hl : ∀ r ∈ l, Good r) (i : Fin n) :
    uL (serve (fun _ => false) l w).1 i = uL l i - (serve (fun _ => false) l w).2.2 i := by
  induction l generalizing w with
  | nil => simp [serve_nil, uL]
  | cons r rs ih =>
    rw [serve_cons]
    have hr := hl r (by simp)
    have ih' := ih (w - min (r.size - r.alloc) w) (fun r'' h'' => hl r'' (by simp [h'']))
    simp only [uL] at ih' ⊢
    simp only [Pi.add_apply]
    rw [hr.1]
    by_cases h : r.ret = i
    · subst h
      simp [List.filter_cons, ih']
      ring
    · have h' : i ≠ r.ret := fun e => h e.symm
      simp [List.filter_cons, h, h', ih']

/-- Exhaustive service: either the stock is used up or every request is fully allocated. -/
private lemma serve_exhaust (l : List (Req n)) (w : ℝ) (hw : 0 ≤ w) (hl : ∀ r ∈ l, Good r) :
    (serve (fun _ => false) l w).2.1 = 0 ∨
      ∀ r ∈ (serve (fun _ => false) l w).1, r.alloc = r.size := by
  induction l generalizing w with
  | nil => right; simp [serve_nil]
  | cons r rs ih =>
    rw [serve_cons]
    have hr := hl r (by simp)
    have hrest : ∀ r'' ∈ rs, Good r'' := fun r'' h'' => hl r'' (by simp [h''])
    rcases le_or_gt (r.size - r.alloc) w with h | h
    · have hm : min (r.size - r.alloc) w = r.size - r.alloc := min_eq_left h
      rcases ih (w - min (r.size - r.alloc) w) (by rw [hm]; linarith) hrest with h1 | h1
      · left; exact h1
      · right
        intro r' hr'
        rcases List.mem_cons.1 hr' with h2 | h2
        · subst h2; simp only [upd_alloc, upd_size, hm]; ring
        · exact h1 r' h2
    · have hm : min (r.size - r.alloc) w = w := min_eq_right h.le
      left
      have : w - min (r.size - r.alloc) w = 0 := by rw [hm]; ring
      rw [this]
      have h0 := serve_conserve rs 0 hrest
      have hsh : ∀ i, 0 ≤ (serve (fun _ => false) rs 0).2.2 i :=
        serve_ship_nonneg rs 0 le_rfl hrest
      have hw0 := serve_w_nonneg rs 0 le_rfl
      have hs : 0 ≤ ∑ i, (serve (fun _ => false) rs 0).2.2 i :=
        Finset.sum_nonneg fun i _ => hsh i
      linarith

private lemma upd_zero (r : Req n) (hr : Good r) : upd r 0 = r := by
  obtain ⟨h1, -, -⟩ := hr
  cases r
  simp only [upd, add_zero, Req.mk.injEq, true_and, and_true]
  simp only at h1
  exact h1.symm

/-- Serving with no stock changes nothing. -/
private lemma serve_zero (l : List (Req n)) (hl : ∀ r ∈ l, Good r) :
    (serve (fun _ => false) l 0).1 = l := by
  induction l with
  | nil => rfl
  | cons r rs ih =>
    rw [serve_cons]
    have hr := hl r (by simp)
    have hm : min (r.size - r.alloc) 0 = 0 := min_eq_right (by linarith [hr.2.2])
    simp only [hm, sub_zero, upd_zero r hr, List.cons.injEq, true_and]
    exact ih fun r'' h'' => hl r'' (by simp [h''])

private lemma ind_add_le (K : Fin n → ℝ) (hK : ∀ i, 0 ≤ K i) (u v : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    ∑ i, K i * (if 0 < u i + v i then 1 else 0)
      ≤ ∑ i, K i * (if 0 < u i then 1 else 0) + ∑ i, K i * (if 0 < v i then 1 else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hK i)
  have := hu i
  have := hv i
  split_ifs <;> linarith

private lemma ind_single (K : Fin n → ℝ) (j : Fin n) (a : ℝ) :
    ∑ i, K i * (if 0 < Pi.single (M := fun _ => ℝ) j a i then 1 else 0)
      = if 0 < a then K j else 0 := by
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same]
    split_ifs <;> simp
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij]
    simp
  · simp

private lemma zK_cons (K : Fin n → ℝ) (r : Req n) (l : List (Req n)) :
    zK K (r :: l) = (if r.alloc = 0 then K r.ret else 0) + zK K l := by
  unfold zK
  by_cases h : r.alloc = 0 <;> simp [List.filter_cons, h]

private lemma zK_nonneg (K : Fin n → ℝ) (hK : ∀ i, 0 ≤ K i) (l : List (Req n)) : 0 ≤ zK K l := by
  induction l with
  | nil => simp [zK]
  | cons r rs ih =>
    rw [zK_cons]
    have := hK r.ret
    split_ifs <;> linarith

/-- Lemma 7, one period, when no request has been allocated yet. -/
private lemma serve_charge_zero (K : Fin n → ℝ) (hK : ∀ i, 0 ≤ K i) (l : List (Req n)) (w : ℝ)
    (hw : 0 ≤ w) (hl : ∀ r ∈ l, Good r) (h0 : ∀ r ∈ l, r.alloc = 0) :
    ∑ i, K i * (if 0 < (serve (fun _ => false) l w).2.2 i then 1 else 0)
      + zK K (serve (fun _ => false) l w).1 ≤ zK K l := by
  induction l generalizing w with
  | nil => simp [serve_nil, zK]
  | cons r rs ih =>
    rw [serve_cons]
    have hr := hl r (by simp)
    have hr0 := h0 r (by simp)
    have hrest : ∀ r'' ∈ rs, Good r'' := fun r'' h'' => hl r'' (by simp [h''])
    have hrest0 : ∀ r'' ∈ rs, r''.alloc = 0 := fun r'' h'' => h0 r'' (by simp [h''])
    set a := min (r.size - r.alloc) w with ha
    have ha0 : 0 ≤ a := le_min (by linarith [hr.2.2]) hw
    have hwa : 0 ≤ w - a := by linarith [min_le_right (r.size - r.alloc) w]
    have ih' := ih (w - a) hwa hrest hrest0
    simp only
    rw [hr.1, show r.alloc + a - r.alloc = a by ring]
    have hsplit := ind_add_le K hK (serve (fun _ => false) rs (w - a)).2.2
      (Pi.single (M := fun _ => ℝ) r.ret a) (serve_ship_nonneg rs (w - a) hwa hrest)
      (fun i => by
        by_cases h : i = r.ret
        · rw [h, Pi.single_eq_same]; exact ha0
        · rw [Pi.single_eq_of_ne h])
    rw [ind_single] at hsplit
    rw [zK_cons, zK_cons]
    simp only [upd_alloc, upd_ret, hr0, zero_add, if_true]
    have hKr := hK r.ret
    have : (if 0 < a then K r.ret else 0) + (if a = 0 then K r.ret else 0) = K r.ret := by
      rcases lt_or_eq_of_le ha0 with h | h
      · simp [h, h.ne']
      · simp [← h]
    simp only [Pi.add_apply] at hsplit ⊢
    linarith

/-- Lemma 7, one period: only the head request can be continued. -/
private lemma serve_charge (K : Fin n → ℝ) (hK : ∀ i, 0 ≤ K i) (Km : ℝ) (hKm : ∀ i, K i ≤ Km)
    (hKm0 : 0 ≤ Km) (l : List (Req n)) (w : ℝ) (hw : 0 ≤ w) (hl : ∀ r ∈ l, Good r)
    (htail : ∀ r ∈ l.tail, r.alloc = 0) (ind : ℝ) (hind0 : 0 ≤ ind)
    (hind : 0 < w → (∃ r ∈ l, 0 < r.alloc) → 1 ≤ ind) :
    ∑ i, K i * (if 0 < (serve (fun _ => false) l w).2.2 i then 1 else 0)
      + zK K (serve (fun _ => false) l w).1 ≤ zK K l + Km * ind := by
  have hKi : 0 ≤ Km * ind := mul_nonneg hKm0 hind0
  cases l with
  | nil =>
    simp only [serve_nil, Pi.zero_apply, lt_irrefl, if_false, mul_zero, Finset.sum_const_zero,
      zero_add]
    simp only [zK, List.filter_nil, List.map_nil, List.sum_nil, zero_add]
    exact hKi
  | cons r rs =>
    rw [serve_cons]
    have hr := hl r (by simp)
    have hrest : ∀ r'' ∈ rs, Good r'' := fun r'' h'' => hl r'' (by simp [h''])
    have hrest0 : ∀ r'' ∈ rs, r''.alloc = 0 := fun r'' h'' => htail r'' (by simpa using h'')
    set a := min (r.size - r.alloc) w with ha
    have ha0 : 0 ≤ a := le_min (by linarith [hr.2.2]) hw
    have haw : a ≤ w := min_le_right _ _
    have hwa : 0 ≤ w - a := by linarith
    have hz := serve_charge_zero K hK rs (w - a) hwa hrest hrest0
    simp only
    rw [hr.1, show r.alloc + a - r.alloc = a by ring]
    have hsplit := ind_add_le K hK (serve (fun _ => false) rs (w - a)).2.2
      (Pi.single (M := fun _ => ℝ) r.ret a) (serve_ship_nonneg rs (w - a) hwa hrest)
      (fun i => by
        by_cases h : i = r.ret
        · rw [h, Pi.single_eq_same]; exact ha0
        · rw [Pi.single_eq_of_ne h])
    rw [ind_single] at hsplit
    rw [zK_cons, zK_cons]
    simp only [upd_alloc, upd_ret]
    have hKr := hK r.ret
    have hKmr := hKm r.ret
    have hkey : (if 0 < a then K r.ret else 0) + (if r.alloc + a = 0 then K r.ret else 0)
        ≤ (if r.alloc = 0 then K r.ret else 0) + Km * ind := by
      rcases lt_or_eq_of_le hr.2.1 with h | h
      · have h1 : ¬ r.alloc + a = 0 := by linarith
        have h2 : ¬ r.alloc = 0 := h.ne'
        rw [if_neg h1, if_neg h2]
        by_cases h3 : 0 < a
        · have h4 : 1 ≤ ind := hind (by linarith) ⟨r, by simp, h⟩
          rw [if_pos h3]
          nlinarith
        · rw [if_neg h3]
          linarith
      · rw [← h]
        simp only [zero_add, if_true]
        rcases lt_or_eq_of_le ha0 with h' | h'
        · simp only [h', if_true, h'.ne', if_false]; linarith
        · simp only [← h', lt_irrefl, if_false, if_true]; linarith
    simp only [Pi.add_apply] at hsplit ⊢
    have e1 := add_le_add hsplit (le_refl ((if r.alloc + a = 0 then K r.ret else 0)
      + zK K (serve (fun _ => false) rs (w - a)).1))
    refine le_trans e1 ?_
    linarith

private lemma flt_cons (r : Req n) (l : List (Req n)) :
    flt (r :: l) = if r.shipped < r.size then r :: flt l else flt l := by
  unfold flt
  by_cases h : r.shipped < r.size <;> simp [List.filter_cons, h]

private lemma mem_flt {l : List (Req n)} {r : Req n} (h : r ∈ flt l) : r ∈ l ∧ r.shipped < r.size := by
  unfold flt at h
  simpa using h

/-- After serving and filtering, only the head can carry an allocation (from an unallocated queue). -/
private lemma serve_head_zero (l : List (Req n)) (w : ℝ) (hw : 0 ≤ w) (hl : ∀ r ∈ l, Good r)
    (h0 : ∀ r ∈ l, r.alloc = 0) :
    ∀ r' ∈ (flt (serve (fun _ => false) l w).1).tail, r'.alloc = 0 := by
  induction l generalizing w with
  | nil => simp [serve_nil, flt]
  | cons r rs ih =>
    rw [serve_cons]
    have hr := hl r (by simp)
    have hr0 := h0 r (by simp)
    have hrest : ∀ r'' ∈ rs, Good r'' := fun r'' h'' => hl r'' (by simp [h''])
    have hrest0 : ∀ r'' ∈ rs, r''.alloc = 0 := fun r'' h'' => h0 r'' (by simp [h''])
    simp only
    rw [flt_cons]
    rcases le_or_gt (r.size - r.alloc) w with h | h
    · have hm : min (r.size - r.alloc) w = r.size - r.alloc := min_eq_left h
      have hns : ¬ (upd r (min (r.size - r.alloc) w)).shipped < (upd r (min (r.size - r.alloc) w)).size := by
        simp only [upd_shipped, upd_size, hm]; linarith
      rw [if_neg hns]
      exact ih _ (by rw [hm]; linarith) hrest hrest0
    · have hm : min (r.size - r.alloc) w = w := min_eq_right h.le
      have hs : (upd r (min (r.size - r.alloc) w)).shipped < (upd r (min (r.size - r.alloc) w)).size := by
        simp only [upd_shipped, upd_size, hm]; linarith
      rw [if_pos hs, List.tail_cons, show w - min (r.size - r.alloc) w = 0 by rw [hm]; ring,
        serve_zero rs hrest]
      intro r' hr'
      exact hrest0 r' (mem_flt hr').1

/-- After serving and filtering, only the head can carry an allocation. -/
private lemma serve_head (l : List (Req n)) (w : ℝ) (hw : 0 ≤ w) (hl : ∀ r ∈ l, Good r)
    (htail : ∀ r ∈ l.tail, r.alloc = 0) :
    ∀ r' ∈ (flt (serve (fun _ => false) l w).1).tail, r'.alloc = 0 := by
  cases l with
  | nil => simp [serve_nil, flt]
  | cons r rs =>
    rw [serve_cons]
    have hr := hl r (by simp)
    have hrest : ∀ r'' ∈ rs, Good r'' := fun r'' h'' => hl r'' (by simp [h''])
    have hrest0 : ∀ r'' ∈ rs, r''.alloc = 0 := fun r'' h'' => htail r'' (by simpa using h'')
    simp only
    rw [flt_cons]
    rcases le_or_gt (r.size - r.alloc) w with h | h
    · have hm : min (r.size - r.alloc) w = r.size - r.alloc := min_eq_left h
      have hns : ¬ (upd r (min (r.size - r.alloc) w)).shipped < (upd r (min (r.size - r.alloc) w)).size := by
        simp only [upd_shipped, upd_size, hm]; linarith
      rw [if_neg hns]
      exact serve_head_zero rs _ (by rw [hm]; linarith) hrest hrest0
    · have hm : min (r.size - r.alloc) w = w := min_eq_right h.le
      have hs : (upd r (min (r.size - r.alloc) w)).shipped < (upd r (min (r.size - r.alloc) w)).size := by
        simp only [upd_shipped, upd_size, hm]; linarith
      rw [if_pos hs, List.tail_cons, show w - min (r.size - r.alloc) w = 0 by rw [hm]; ring,
        serve_zero rs hrest]
      intro r' hr'
      exact hrest0 r' (mem_flt hr').1

private lemma uL_cons (r : Req n) (l : List (Req n)) (i : Fin n) :
    uL (r :: l) i = (if r.ret = i then r.size - r.alloc else 0) + uL l i := by
  unfold uL
  by_cases h : r.ret = i <;> simp [List.filter_cons, h]

/-- Filtering out fully shipped requests does not change the unallocated quantities. -/
private lemma uL_flt (l : List (Req n)) (hl : ∀ r ∈ l, Good r) (i : Fin n) : uL (flt l) i = uL l i := by
  induction l with
  | nil => rfl
  | cons r rs ih =>
    have hr := hl r (by simp)
    have ih' := ih fun r'' h'' => hl r'' (by simp [h''])
    rw [flt_cons]
    split_ifs with h
    · rw [uL_cons, uL_cons, ih']
    · rw [uL_cons, ih']
      have : r.size - r.alloc = 0 := by
        have := hr.1; have := hr.2.2; simp only [not_lt] at h; linarith
      simp [this]

private lemma zK_flt_le (K : Fin n → ℝ) (hK : ∀ i, 0 ≤ K i) (l : List (Req n)) :
    zK K (flt l) ≤ zK K l := by
  induction l with
  | nil => simp [flt, zK]
  | cons r rs ih =>
    rw [flt_cons]
    split_ifs with h
    · rw [zK_cons, zK_cons]; linarith
    · rw [zK_cons]
      have := hK r.ret
      have : 0 ≤ (if r.alloc = 0 then K r.ret else 0) := by split_ifs <;> linarith
      linarith

private lemma uL_nonneg (l : List (Req n)) (hl : ∀ r ∈ l, Good r) (i : Fin n) : 0 ≤ uL l i := by
  induction l with
  | nil => simp [uL]
  | cons r rs ih =>
    rw [uL_cons]
    have hr := hl r (by simp)
    have := ih fun r'' h'' => hl r'' (by simp [h''])
    have : 0 ≤ (if r.ret = i then r.size - r.alloc else 0) := by
      split_ifs <;> linarith [hr.2.2]
    linarith

/-! ### Lists of new requests -/

private lemma sum_finRange_ite (p : Fin n → Bool) (h : Fin n → ℝ) :
    (((List.finRange n).filter p).map h).sum = ∑ j, if p j then h j else 0 := by
  rw [sum_map_filter_eq, Fin.sum_univ_def]

private noncomputable def newL (q o : Fin n → ℝ) (t : ℕ) : List (Req n) :=
  ((List.finRange n).filter (fun i => 0 < q i)).map (fun i =>
    ({ ret := i, size := q i, alloc := 0, shipped := 0, offset := o i, born := t } : Req n))

private lemma newL_mem {q o : Fin n → ℝ} {t : ℕ} {r : Req n} (h : r ∈ newL q o t) :
    r.alloc = 0 ∧ r.shipped = 0 ∧ 0 < r.size := by
  unfold newL at h
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨rfl, rfl, hi⟩

private lemma newL_good {q o : Fin n → ℝ} {t : ℕ} : ∀ r ∈ newL q o t, Good r := fun r h => by
  obtain ⟨h1, h2, h3⟩ := newL_mem h
  exact ⟨by rw [h1, h2], by rw [h1], by rw [h1]; exact h3.le⟩

private lemma uL_newL (q o : Fin n → ℝ) (t : ℕ) (i : Fin n) :
    uL (newL q o t) i = if 0 < q i then q i else 0 := by
  unfold uL newL
  rw [sum_map_filter_eq, List.map_map]
  have : ((fun r : Req n => if decide (r.ret = i) then r.size - r.alloc else 0) ∘ fun j : Fin n =>
      ({ ret := j, size := q j, alloc := 0, shipped := 0, offset := o j, born := t } : Req n))
      = fun j => if j = i then q j else 0 := by
    funext j; simp
  rw [this, sum_finRange_ite, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

private lemma zK_newL (K : Fin n → ℝ) (q o : Fin n → ℝ) (t : ℕ) :
    zK K (newL q o t) = ∑ i, if 0 < q i then K i else 0 := by
  unfold zK newL
  rw [sum_map_filter_eq, List.map_map]
  have : ((fun r : Req n => if decide (r.alloc = 0) then K r.ret else 0) ∘ fun j : Fin n =>
      ({ ret := j, size := q j, alloc := 0, shipped := 0, offset := o j, born := t } : Req n))
      = fun j => K j := by
    funext j; simp
  rw [this, sum_finRange_ite]
  simp

private lemma mapIdx_const {α β : Type} (f : α → β) (l : List α) :
    l.mapIdx (fun _ a => f a) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapIdx_cons, ih]

/-! ### One period of the FIFO engine -/

section engine

variable (N : Network n) (c : FIFOChoice n)

private abbrev rule0 : OffsetRule n := fun _ _ _ _ _ => 0

/-- The supplier position computed in step 2. -/
private noncomputable def posE (st : EngState n) (t : ℕ) : ℝ :=
  st.Wbar + ∑ i, reserve st i + supInTransit N.L0 st t + ∑ i, (physPos N.L st t i - c.a i)

private noncomputable def q0E (st : EngState n) (t : ℕ) : ℝ :=
  if posE N c st t ≤ c.s0 then c.S0 - posE N c st t else 0

private lemma phaseA_snd (st : EngState n) (t : ℕ) :
    (phaseA N.L0 N.L c.params rule0 t st).2 = q0E N c st t := rfl

private lemma phaseA_fst (st : EngState n) (t : ℕ) :
    (phaseA N.L0 N.L c.params rule0 t st).1 =
      { st with
        Wbar := if N.L0 = 0 then st.Wbar + q0E N c st t else st.Wbar
        supPipe := if N.L0 = 0 then st.supPipe
          else Function.update st.supPipe (t + N.L0) (st.supPipe (t + N.L0) + q0E N c st t)
        queue := st.queue ++ newL (reqSize N.L c.params st t) (fun _ => 0) t
        nOrd := st.nOrd + ((List.finRange n).filter (fun i => 0 < reqSize N.L c.params st t i)).length } := by
  simp only [phaseA, newL, FIFOChoice.params, Bool.false_eq_true, if_false]
  rw [mapIdx_const]
  rfl

/-- The step of a running (or just started) period, in terms of the state after the receipts. -/
private lemma runStep_eq (st : EngState n) (t : ℕ) :
    runStep N.L0 N.L c.params rule0 t st =
      (sendOut N.L t
        (serve (fun _ => false) (st.queue ++ newL (reqSize N.L c.params st t) (fun _ => 0) t)
          (if N.L0 = 0 then st.Wbar + q0E N c st t else st.Wbar)).2.2
        { st with
          Wbar := (serve (fun _ => false) (st.queue ++ newL (reqSize N.L c.params st t) (fun _ => 0) t)
            (if N.L0 = 0 then st.Wbar + q0E N c st t else st.Wbar)).2.1
          supPipe := if N.L0 = 0 then st.supPipe
            else Function.update st.supPipe (t + N.L0) (st.supPipe (t + N.L0) + q0E N c st t)
          queue := flt (serve (fun _ => false) (st.queue ++ newL (reqSize N.L c.params st t) (fun _ => 0) t)
            (if N.L0 = 0 then st.Wbar + q0E N c st t else st.Wbar)).1
          nOrd := st.nOrd + ((List.finRange n).filter (fun i => 0 < reqSize N.L c.params st t i)).length },
        q0E N c st t,
        (serve (fun _ => false) (st.queue ++ newL (reqSize N.L c.params st t) (fun _ => 0) t)
          (if N.L0 = 0 then st.Wbar + q0E N c st t else st.Wbar)).2.2) := by
  unfold runStep phaseB
  dsimp only
  rw [phaseA_fst, phaseA_snd]
  rfl

end engine

/-! ### Bookkeeping along the run -/

private lemma uL_append (l1 l2 : List (Req n)) (i : Fin n) : uL (l1 ++ l2) i = uL l1 i + uL l2 i := by
  unfold uL
  simp [List.filter_append, List.sum_append]

private lemma zK_append (K : Fin n → ℝ) (l1 l2 : List (Req n)) : zK K (l1 ++ l2) = zK K l1 + zK K l2 := by
  unfold zK
  simp [List.filter_append, List.sum_append]

private lemma reserve_zero (st : EngState n) (h : ∀ r ∈ st.queue, Good r) (i : Fin n) :
    reserve st i = 0 := by
  unfold reserve
  apply List.sum_eq_zero
  intro a ha
  simp only [List.mem_map, List.mem_filter] at ha
  obtain ⟨r, ⟨hr, -⟩, rfl⟩ := ha
  rw [(h r hr).1, sub_self]

private lemma tail_append_alloc (l1 l2 : List (Req n)) (h1 : ∀ r ∈ l1.tail, r.alloc = 0)
    (h2 : ∀ r ∈ l2, r.alloc = 0) : ∀ r ∈ (l1 ++ l2).tail, r.alloc = 0 := by
  cases l1 with
  | nil =>
    intro r hr
    exact h2 r (List.mem_of_mem_tail (by simpa using hr))
  | cons a l1 =>
    intro r hr
    simp only [List.cons_append, List.tail_cons, List.mem_append] at hr
    rcases hr with hr | hr
    · exact h1 r (by simpa using hr)
    · exact h2 r hr

/-- `∑_{k < L} f (t + k)` split into its first term and the rest of the window. -/
private lemma window_sum (f : ℕ → ℝ) (t L : ℕ) :
    (if t < t + L then f t else 0) + ∑ k ∈ Finset.range L, (if t + 1 + k < t + L then f (t + 1 + k) else 0)
      = ∑ k ∈ Finset.range L, f (t + k) := by
  cases L with
  | zero => simp
  | succ m =>
    rw [if_pos (by omega),
      Finset.sum_range_succ (fun k => if t + 1 + k < t + (m + 1) then f (t + 1 + k) else 0),
      if_neg (by omega), add_zero, Finset.sum_range_succ' (fun k => f (t + k)), add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (by have := Finset.mem_range.1 hk; omega)]
    congr 1
    omega

section run

variable (N : Network n) (x : InitState n) (c : FIFOChoice n) (d : ℕ → DemandVec n)

private noncomputable def ordE (t : ℕ) : ℝ := (fifoStep N c t (fifoRun N x c d t)).2.1
private noncomputable def dispE (t : ℕ) (i : Fin n) : ℝ := (fifoStep N c t (fifoRun N x c d t)).2.2 i
private noncomputable def supArrE (r : ℕ) : ℝ :=
  if r < N.L0 then x.supPipe r else ordE N x c d (r - N.L0)
private noncomputable def retArrE (i : Fin n) (r : ℕ) : ℝ :=
  if r < N.L i then x.retPipe i r else dispE N x c d (r - N.L i) i
private noncomputable def BB (i : Fin n) : ℝ := x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
private noncomputable def retPosE (i : Fin n) (t : ℕ) : ℝ :=
  BB N x i + ∑ r ∈ Finset.range (t + 1), dispE N x c d r i - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)

private lemma sum_supArrE (t : ℕ) :
    ∑ r ∈ Finset.range (t + N.L0), supArrE N x c d r
      = ∑ s ∈ Finset.range N.L0, x.supPipe s + ∑ r ∈ Finset.range t, ordE N x c d r := by
  rw [add_comm t, Finset.sum_range_add]
  congr 1
  · exact Finset.sum_congr rfl fun r hr => by
      simp [supArrE, Finset.mem_range.1 hr]
  · exact Finset.sum_congr rfl fun r _ => by
      simp [supArrE]

private lemma sum_retArrE (i : Fin n) (t : ℕ) :
    ∑ r ∈ Finset.range (t + N.L i), retArrE N x c d i r
      = ∑ s ∈ Finset.range (N.L i), x.retPipe i s + ∑ r ∈ Finset.range t, dispE N x c d r i := by
  rw [add_comm t, Finset.sum_range_add]
  congr 1
  · exact Finset.sum_congr rfl fun r hr => by
      simp [retArrE, Finset.mem_range.1 hr]
  · exact Finset.sum_congr rfl fun r _ => by
      simp [retArrE]

/-- The physical position of retailer `i` computed in step 1, from the run invariants. -/
private lemma physPos_eq (st : EngState n) (t : ℕ) (i : Fin n)
    (hI : st.I i = x.I i + ∑ r ∈ Finset.range t, (retArrE N x c d i r - ((d r i : ℝ≥0) : ℝ))
      + (if t < t + N.L i then retArrE N x c d i t else 0))
    (hP : ∀ t', t + 1 ≤ t' → st.retPipe i t' = if t' < t + N.L i then retArrE N x c d i t' else 0) :
    physPos N.L st t i = BB N x i + ∑ r ∈ Finset.range t, dispE N x c d r i
      - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) := by
  unfold physPos inTransit
  rw [hI]
  have h1 : ∑ k ∈ Finset.range (N.L i), st.retPipe i (t + 1 + k)
      = ∑ k ∈ Finset.range (N.L i), (if t + 1 + k < t + N.L i then retArrE N x c d i (t + 1 + k) else 0) :=
    Finset.sum_congr rfl fun k _ => hP _ (by omega)
  rw [h1, Finset.sum_sub_distrib]
  have h2 := window_sum (retArrE N x c d i) t (N.L i)
  have h3 := sum_retArrE N x c d i t
  rw [Finset.sum_range_add] at h3
  unfold BB
  linarith

/-- Warehouse stock plus supplier stock in transit, after the receipts of period `t`. -/
private lemma wbar_transit_eq (st : EngState n) (t : ℕ)
    (hW : st.Wbar = x.W + ∑ r ∈ Finset.range t, (supArrE N x c d r - ∑ i, dispE N x c d r i)
      + (if t < t + N.L0 then supArrE N x c d t else 0))
    (hP : ∀ t', t + 1 ≤ t' → st.supPipe t' = if t' < t + N.L0 then supArrE N x c d t' else 0) :
    st.Wbar + supInTransit N.L0 st t = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ r ∈ Finset.range t, ordE N x c d r - ∑ r ∈ Finset.range t, ∑ i, dispE N x c d r i := by
  unfold supInTransit
  rw [hW]
  have h1 : ∑ k ∈ Finset.range N.L0, st.supPipe (t + 1 + k)
      = ∑ k ∈ Finset.range N.L0, (if t + 1 + k < t + N.L0 then supArrE N x c d (t + 1 + k) else 0) :=
    Finset.sum_congr rfl fun k _ => hP _ (by omega)
  rw [h1, Finset.sum_sub_distrib]
  have h2 := window_sum (supArrE N x c d) t N.L0
  have h3 := sum_supArrE N x c d t
  rw [Finset.sum_range_add] at h3
  linarith

end run

/-! ### The run invariant -/

section inv

variable (N : Network n) (x : InitState n) (c : FIFOChoice n) (d : ℕ → DemandVec n)

private lemma fifoStep_run (t : ℕ) (st : EngState n) (h : st.running = true) :
    fifoStep N c t st = runStep N.L0 N.L c.params rule0 t (receive st t) := by
  unfold fifoStep
  dsimp only
  rw [if_pos (show (receive st t).running = true from h)]

private lemma fifoStep_start (t : ℕ) (st : EngState n) (h : st.running = false)
    (hc : N.Tpipe ≤ t + 1 ∧ ∀ i, (receive st t).I i ≤ c.S i) :
    fifoStep N c t st = runStep N.L0 N.L c.params rule0 t
      (startWith (receive st t) t (fun i => c.S i - (receive st t).I i) (fun _ => 0)) := by
  unfold fifoStep
  dsimp only
  rw [if_neg (show ¬ (receive st t).running = true by simp [receive, h]), if_pos hc]

private lemma fifoStep_prep (t : ℕ) (st : EngState n) (h : st.running = false)
    (hc : ¬ (N.Tpipe ≤ t + 1 ∧ ∀ i, (receive st t).I i ≤ c.S i)) :
    fifoStep N c t st = (receive st t, 0, 0) := by
  unfold fifoStep
  dsimp only
  rw [if_neg (show ¬ (receive st t).running = true by simp [receive, h]), if_neg hc]

private noncomputable def QnE (st : EngState n) (t : ℕ) : List (Req n) :=
  st.queue ++ newL (reqSize N.L c.params st t) (fun _ => 0) t

private noncomputable def WnE (st : EngState n) (t : ℕ) : ℝ :=
  if N.L0 = 0 then st.Wbar + q0E N c st t else st.Wbar

private noncomputable def resE (st : EngState n) (t : ℕ) : List (Req n) × ℝ × (Fin n → ℝ) :=
  serve (fun _ => false) (QnE N c st t) (WnE N c st t)

/-- Fields of the state after a running step from the state `st''` after receipts (and start). -/
private lemma run_fields (t : ℕ) (st'' : EngState n) :
    (runStep N.L0 N.L c.params rule0 t st'').2.1 = q0E N c st'' t ∧
      (runStep N.L0 N.L c.params rule0 t st'').2.2 = (resE N c st'' t).2.2 ∧
      (runStep N.L0 N.L c.params rule0 t st'').1.running = st''.running ∧
      (runStep N.L0 N.L c.params rule0 t st'').1.Wbar = (resE N c st'' t).2.1 ∧
      (∀ i, (runStep N.L0 N.L c.params rule0 t st'').1.I i
        = if N.L i = 0 then st''.I i + (resE N c st'' t).2.2 i else st''.I i) ∧
      (runStep N.L0 N.L c.params rule0 t st'').1.supPipe = (if N.L0 = 0 then st''.supPipe
        else Function.update st''.supPipe (t + N.L0) (st''.supPipe (t + N.L0) + q0E N c st'' t)) ∧
      (∀ i, (runStep N.L0 N.L c.params rule0 t st'').1.retPipe i = if N.L i = 0 then st''.retPipe i
        else Function.update (st''.retPipe i) (t + N.L i) (st''.retPipe i (t + N.L i)
          + (resE N c st'' t).2.2 i)) ∧
      (runStep N.L0 N.L c.params rule0 t st'').1.queue = flt (resE N c st'' t).1 := by
  rw [runStep_eq]
  exact ⟨rfl, rfl, rfl, rfl, fun i => rfl, rfl, fun i => rfl, rfl⟩

end inv

section inv2

variable (N : Network n) (x : InitState n) (c : FIFOChoice n) (d : ℕ → DemandVec n)
  (act : ℕ → Prop) [DecidablePred act] (Yp : ℕ → ℝ) (Ph : ℕ → Fin n → ℝ) (K : Fin n → ℝ) (Km : ℝ)

private noncomputable def ReqE (r : ℕ) : ℝ :=
  if 0 < r ∧ act (r - 1) then ∑ i, K i * (if Ph (r - 1) i - ((d (r - 1) i : ℝ≥0) : ℝ) ≤ c.s i
    ∧ Ph (r - 1) i - ((d (r - 1) i : ℝ≥0) : ℝ) < c.S i then 1 else 0) else 0

private structure RInv (t : ℕ) : Prop where
  run : (fifoRun N x c d t).running = true ↔ (0 < t ∧ act (t - 1))
  wbar : (fifoRun N x c d t).Wbar
    = x.W + ∑ r ∈ Finset.range t, (supArrE N x c d r - ∑ i, dispE N x c d r i)
  sp : ∀ t', t ≤ t' → (fifoRun N x c d t).supPipe t' = if t' < t + N.L0 then supArrE N x c d t' else 0
  inv : ∀ i, (fifoRun N x c d t).I i
    = x.I i + ∑ r ∈ Finset.range t, (retArrE N x c d i r - ((d r i : ℝ≥0) : ℝ))
  rp : ∀ i t', t ≤ t' →
    (fifoRun N x c d t).retPipe i t' = if t' < t + N.L i then retArrE N x c d i t' else 0
  good : ∀ r ∈ (fifoRun N x c d t).queue, Good r ∧ r.alloc < r.size
  head : ∀ r ∈ (fifoRun N x c d t).queue.tail, r.alloc = 0
  fifo : (fifoRun N x c d t).queue ≠ [] → (fifoRun N x c d t).Wbar = 0
  wnn : 0 ≤ (fifoRun N x c d t).Wbar
  emp : (fifoRun N x c d t).running = false → (fifoRun N x c d t).queue = []
  prep : (fifoRun N x c d t).running = false →
    ∀ r < t, ordE N x c d r = 0 ∧ ∀ i, dispE N x c d r i = 0
  ord : ∀ r < t, ordE N x c d r = if act r ∧ Yp r ≤ c.s0 then c.S0 - Yp r else 0
  ph : ∀ t', t = t' + 1 → act t' →
    ∀ i, Ph t' i = retPosE N x c d i t' + uL (fifoRun N x c d t).queue i
  l7 : ∑ r ∈ Finset.range t, ∑ i, K i * (if 0 < dispE N x c d r i then 1 else 0)
      + zK K (fifoRun N x c d t).queue
    ≤ ∑ r ∈ Finset.range t, ReqE c d act Ph K r
      + Km * ((n : ℝ) * (if (fifoRun N x c d t).running = true then 1 else 0)
        + ∑ r ∈ Finset.range t, (if 0 < supArrE N x c d r then 1 else 0))
  dnn : ∀ r < t, ∀ i, 0 ≤ dispE N x c d r i

private lemma rinv_zero (hx : x.Valid) : RInv N x c d act Yp Ph K Km 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [fifoRun, initEngState]
  · simp [fifoRun, initEngState]
  · intro t' _
    simp only [fifoRun, initEngState, zero_add, supArrE]
    split_ifs <;> rfl
  · intro i; simp [fifoRun, initEngState]
  · intro i t' _
    simp only [fifoRun, initEngState, zero_add, retArrE]
    split_ifs <;> rfl
  · simp [fifoRun, initEngState]
  · simp [fifoRun, initEngState]
  · simp [fifoRun, initEngState]
  · simpa [fifoRun, initEngState] using hx.1
  · simp [fifoRun, initEngState]
  · intro _ r hr; omega
  · intro r hr; omega
  · intro t' h; omega
  · simp [fifoRun, initEngState, zK]
  · intro r hr; omega

end inv2

section steps

variable (N : Network n) (x : InitState n) (c : FIFOChoice n) (d : ℕ → DemandVec n)
  (act : ℕ → Prop) [DecidablePred act] (Yp : ℕ → ℝ) (Ph : ℕ → Fin n → ℝ) (K : Fin n → ℝ) (Km : ℝ)

private lemma run_succ (t : ℕ) :
    fifoRun N x c d (t + 1) = applyDemand (fifoStep N c t (fifoRun N x c d t)).1 (d t) := rfl

private lemma act_mono
    (hact : ∀ t, act t ↔ (N.Tpipe ≤ t + 1 ∧ ∀ i, x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i)) (t : ℕ) (h : act t) : act (t + 1) := by
  rw [hact] at h ⊢
  refine ⟨by omega, fun i => ?_⟩
  have := h.2 i
  rw [Finset.sum_range_succ]
  have : (0 : ℝ) ≤ ((d t i : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  linarith

private lemma Yp_sum
    (hY : ∀ t, Yp (t + 1) = (if act t ∧ Yp t ≤ c.s0 then c.S0 else Yp t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ)) :
    ∀ t, Yp t = Yp 0 + ∑ r ∈ Finset.range t, ((if act r ∧ Yp r ≤ c.s0 then c.S0 else Yp r) - Yp r)
      - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ)
  | 0 => by simp
  | t + 1 => by
    have h1 := Yp_sum hY t
    have h2 := hY t
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

/-- The supplier position of a period, after the receipts, is `Yp t`. -/
private lemma posE_eq
    (hY0 : Yp 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i))
    (hY : ∀ t, Yp (t + 1) = (if act t ∧ Yp t ≤ c.s0 then c.S0 else Yp t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
    (t : ℕ) (hI : RInv N x c d act Yp Ph K Km t) (st : EngState n)
    (hW : st.Wbar = (fifoRun N x c d t).Wbar + (fifoRun N x c d t).supPipe t)
    (hIe : ∀ i, st.I i = (fifoRun N x c d t).I i + (fifoRun N x c d t).retPipe i t)
    (hS : st.supPipe = (fifoRun N x c d t).supPipe) (hR : st.retPipe = (fifoRun N x c d t).retPipe)
    (hG : ∀ r ∈ st.queue, Good r) :
    posE N c st t = Yp t := by
  have hphys : ∀ i, physPos N.L st t i = BB N x i + ∑ r ∈ Finset.range t, dispE N x c d r i
      - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) := by
    intro i
    refine physPos_eq N x c d st t i ?_ ?_
    · rw [hIe, hI.inv i, hI.rp i t le_rfl]
    · intro t' ht'; rw [hR]; exact hI.rp i t' (by omega)
  have hwt := wbar_transit_eq N x c d st t (by rw [hW, hI.wbar, hI.sp t le_rfl])
    (fun t' ht' => by rw [hS]; exact hI.sp t' (by omega))
  have hres : ∀ i, reserve st i = 0 := reserve_zero st hG
  unfold posE
  simp only [hres, Finset.sum_const_zero, add_zero, hphys]
  have hord : ∀ r ∈ Finset.range t, ordE N x c d r
      = (if act r ∧ Yp r ≤ c.s0 then c.S0 else Yp r) - Yp r := by
    intro r hr
    rw [hI.ord r (Finset.mem_range.1 hr)]
    split_ifs <;> ring
  rw [Yp_sum c d act Yp hY t, ← Finset.sum_congr rfl hord, hY0]
  have hcomm : ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ)
      = ∑ i, ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) := Finset.sum_comm
  have hcomm2 : ∑ r ∈ Finset.range t, ∑ i, dispE N x c d r i
      = ∑ i, ∑ r ∈ Finset.range t, dispE N x c d r i := Finset.sum_comm
  have hsplit : ∑ i, (BB N x i + ∑ r ∈ Finset.range t, dispE N x c d r i
      - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) - c.a i)
      = ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
        + ∑ i, ∑ r ∈ Finset.range t, dispE N x c d r i
        - ∑ i, ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold BB; ring
  rw [hsplit, hcomm]
  linarith

end steps

section running

variable (N : Network n) (x : InitState n) (c : FIFOChoice n) (d : ℕ → DemandVec n)
  (act : ℕ → Prop) [DecidablePred act] (Yp : ℕ → ℝ) (Ph : ℕ → Fin n → ℝ) (K : Fin n → ℝ) (Km : ℝ)

private lemma q0E_nonneg (hs0 : c.s0 ≤ c.S0) (st : EngState n) (t : ℕ) : 0 ≤ q0E N c st t := by
  unfold q0E
  split_ifs with h
  · linarith
  · exact le_rfl

/-- A running (or starting) period: everything except the request positions and Lemma 7. -/
private lemma step_running (hK : ∀ i, 0 ≤ K i) (hKm : ∀ i, K i ≤ Km) (hKm0 : 0 ≤ Km)
    (hx : x.Valid) (hs0 : c.s0 ≤ c.S0)
    (hY0 : Yp 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i))
    (hY : ∀ t, Yp (t + 1) = (if act t ∧ Yp t ≤ c.s0 then c.S0 else Yp t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
    (t : ℕ) (hI : RInv N x c d act Yp Ph K Km t) (st : EngState n)
    (hfs : fifoStep N c t (fifoRun N x c d t) = runStep N.L0 N.L c.params rule0 t st)
    (hW : st.Wbar = (fifoRun N x c d t).Wbar + (fifoRun N x c d t).supPipe t)
    (hIe : ∀ i, st.I i = (fifoRun N x c d t).I i + (fifoRun N x c d t).retPipe i t)
    (hS : st.supPipe = (fifoRun N x c d t).supPipe) (hR : st.retPipe = (fifoRun N x c d t).retPipe)
    (hrun : st.running = true) (hG : ∀ r ∈ st.queue, Good r)
    (hT : ∀ r ∈ st.queue.tail, r.alloc = 0) (hact : act t)
    (hQ : (∃ r ∈ st.queue, 0 < r.alloc) → (fifoRun N x c d t).Wbar = 0)
    (hph : ∀ i, Ph t i = retPosE N x c d i t + (uL (QnE N c st t) i - dispE N x c d t i))
    (hz : ∑ r ∈ Finset.range t, ∑ i, K i * (if 0 < dispE N x c d r i then 1 else 0)
        + zK K (QnE N c st t) + Km * (if 0 < supArrE N x c d t then 1 else 0)
      ≤ ∑ r ∈ Finset.range (t + 1), ReqE c d act Ph K r
        + Km * ((n : ℝ) + ∑ r ∈ Finset.range (t + 1), (if 0 < supArrE N x c d r then 1 else 0))) :
    RInv N x c d act Yp Ph K Km (t + 1) := by
  obtain ⟨h_ord, h_disp, h_run, h_wb, h_I, h_sp, h_rp, h_q⟩ := run_fields N c t st
  set st0 := fifoRun N x c d t with hst0
  have hR1 : fifoRun N x c d (t + 1) = applyDemand (runStep N.L0 N.L c.params rule0 t st).1 (d t) := by
    rw [run_succ, hfs]
  have e_ord : ordE N x c d t = q0E N c st t := by unfold ordE; rw [hfs, h_ord]
  have e_disp : ∀ i, dispE N x c d t i = (resE N c st t).2.2 i := fun i => by
    unfold dispE; rw [hfs, h_disp]
  have hpos : posE N c st t = Yp t := posE_eq N x c d act Yp Ph K Km hY0 hY t hI st hW hIe hS hR hG
  have e_ord' : ordE N x c d t = if act t ∧ Yp t ≤ c.s0 then c.S0 - Yp t else 0 := by
    rw [e_ord]; unfold q0E; rw [hpos]; simp only [hact, true_and]
  -- the stock available for allocation
  have hsp_t : st0.supPipe t = if t < t + N.L0 then supArrE N x c d t else 0 := hI.sp t le_rfl
  have hWn : WnE N c st t = st0.Wbar + supArrE N x c d t := by
    unfold WnE
    rw [hW, hsp_t]
    by_cases hL : N.L0 = 0
    · rw [if_pos hL, if_neg (by omega), ← e_ord]
      simp [supArrE, hL]
    · rw [if_neg hL, if_pos (by omega)]
  have hsa_nonneg : ∀ r ≤ t, 0 ≤ supArrE N x c d r := by
    intro r hr
    unfold supArrE
    split_ifs with h
    · exact hx.2.1 r
    · rcases Nat.lt_or_ge (r - N.L0) t with h' | h'
      · rw [hI.ord _ h']
        split_ifs with h''
        · linarith [h''.2]
        · exact le_rfl
      · have : r - N.L0 = t := by omega
        rw [this, e_ord]
        exact q0E_nonneg N c hs0 st t
  have hWn0 : 0 ≤ WnE N c st t := by rw [hWn]; linarith [hI.wnn, hsa_nonneg t le_rfl]
  -- the queue served in this period
  have hQG : ∀ r ∈ QnE N c st t, Good r := by
    intro r hr
    unfold QnE at hr
    rcases List.mem_append.1 hr with h | h
    · exact hG r h
    · exact newL_good r h
  have hQT : ∀ r ∈ (QnE N c st t).tail, r.alloc = 0 :=
    tail_append_alloc _ _ hT (fun r h => (newL_mem h).1)
  have hconv := serve_conserve (QnE N c st t) (WnE N c st t) hQG
  have hgood := serve_good (QnE N c st t) (WnE N c st t) hWn0 hQG
  -- fields of the next state
  have f_run : (fifoRun N x c d (t + 1)).running = true := by rw [hR1]; exact h_run.trans hrun
  have f_wb : (fifoRun N x c d (t + 1)).Wbar = (resE N c st t).2.1 := by rw [hR1]; exact h_wb
  have f_q : (fifoRun N x c d (t + 1)).queue = flt (resE N c st t).1 := by rw [hR1]; exact h_q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- run
    rw [f_run]
    simp only [true_iff]
    exact ⟨by omega, by simpa using hact⟩
  · -- wbar
    rw [f_wb, Finset.sum_range_succ]
    have h1 : st0.Wbar = x.W + ∑ r ∈ Finset.range t, (supArrE N x c d r - ∑ i, dispE N x c d r i) :=
      hI.wbar
    have : (resE N c st t).2.1 = WnE N c st t - ∑ i, (resE N c st t).2.2 i := by
      unfold resE at hconv ⊢; linarith
    rw [this, hWn]
    simp only [e_disp]
    linarith
  · -- sp
    intro t' ht'
    have : (fifoRun N x c d (t + 1)).supPipe = (runStep N.L0 N.L c.params rule0 t st).1.supPipe := by
      rw [hR1]; rfl
    rw [this, h_sp, hS]
    by_cases hL : N.L0 = 0
    · rw [if_pos hL, hI.sp t' (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg hL]
      by_cases he : t' = t + N.L0
      · subst he
        rw [Function.update_self, hI.sp _ (by omega), if_neg (by omega), zero_add, if_pos (by omega),
          ← e_ord]
        simp [supArrE]
      · rw [Function.update_of_ne he, hI.sp t' (by omega)]
        by_cases h1 : t' < t + N.L0
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
  · -- inv
    intro i
    have : (fifoRun N x c d (t + 1)).I i = (runStep N.L0 N.L c.params rule0 t st).1.I i
        - ((d t i : ℝ≥0) : ℝ) := by rw [hR1]; rfl
    rw [this, h_I, Finset.sum_range_succ]
    have h1 : st0.I i = x.I i + ∑ r ∈ Finset.range t, (retArrE N x c d i r - ((d r i : ℝ≥0) : ℝ)) :=
      hI.inv i
    have hrp := hI.rp i t le_rfl
    by_cases hL : N.L i = 0
    · rw [if_pos hL, hIe, hrp, if_neg (by omega), ← e_disp]
      have : retArrE N x c d i t = dispE N x c d t i := by simp [retArrE, hL]
      rw [this]
      linarith
    · rw [if_neg hL, hIe, hrp, if_pos (by omega)]
      linarith
  · -- rp
    intro i t' ht'
    have : (fifoRun N x c d (t + 1)).retPipe i = (runStep N.L0 N.L c.params rule0 t st).1.retPipe i := by
      rw [hR1]; rfl
    rw [this, h_rp, hR]
    by_cases hL : N.L i = 0
    · rw [if_pos hL, hI.rp i t' (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg hL]
      by_cases he : t' = t + N.L i
      · subst he
        rw [Function.update_self, hI.rp i _ (by omega), if_neg (by omega), zero_add, if_pos (by omega),
          ← e_disp]
        simp [retArrE]
      · rw [Function.update_of_ne he, hI.rp i t' (by omega)]
        by_cases h1 : t' < t + N.L i
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
  · -- good
    rw [f_q]
    intro r hr
    obtain ⟨hr1, hr2⟩ := mem_flt hr
    have hg := hgood r hr1
    exact ⟨hg, by rw [← hg.1]; exact hr2⟩
  · -- head
    rw [f_q]
    exact serve_head _ _ hWn0 hQG hQT
  · -- fifo
    rw [f_q, f_wb]
    intro hne
    rcases serve_exhaust (QnE N c st t) (WnE N c st t) hWn0 hQG with h | h
    · exact h
    · exfalso
      apply hne
      unfold flt
      rw [List.filter_eq_nil_iff]
      intro r hr
      have hg := hgood r hr
      simp only [decide_eq_true_eq, not_lt]
      rw [hg.1, h r hr]
  · -- wnn
    rw [f_wb]; exact serve_w_nonneg _ _ hWn0
  · -- emp
    rw [f_run]; intro h; exact absurd h (by simp)
  · -- prep
    rw [f_run]; intro h; exact absurd h (by simp)
  · -- ord
    intro r hr
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with h | h
    · exact hI.ord r h
    · subst h; exact e_ord'
  · -- ph
    intro t' ht' _ i
    have ht : t' = t := by omega
    rw [ht]
    have e1 : uL (flt (resE N c st t).1) i = uL (QnE N c st t) i - (resE N c st t).2.2 i := by
      unfold resE
      rw [uL_flt _ (fun r hr => hgood r hr), serve_uL _ _ hQG]
    rw [hph i, f_q, e1, e_disp]
  · -- l7
    rw [f_q, f_run, Finset.sum_range_succ]
    have hch := serve_charge K hK Km hKm hKm0 (QnE N c st t) (WnE N c st t) hWn0 hQG hQT
      (if 0 < supArrE N x c d t then 1 else 0) (by split_ifs <;> norm_num)
      (by
        intro hw ⟨r, hr, hra⟩
        have hr' : r ∈ st.queue := by
          unfold QnE at hr
          rcases List.mem_append.1 hr with h | h
          · exact h
          · exact absurd (newL_mem h).1 hra.ne'
        have h0 := hQ ⟨r, hr', hra⟩
        rw [hWn, h0, zero_add] at hw
        rw [if_pos hw])
    have hfl := zK_flt_le K hK (resE N c st t).1
    simp only [e_disp]
    unfold resE at hch hfl ⊢
    simp only [if_true, mul_one]
    linarith
  · -- dnn
    intro r hr i
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with h | h
    · exact hI.dnn r h i
    · subst h; rw [e_disp]; exact serve_ship_nonneg _ _ hWn0 hQG i

end running

section cases

variable (N : Network n) (x : InitState n) (c : FIFOChoice n) (d : ℕ → DemandVec n)
  (act : ℕ → Prop) [DecidablePred act] (Yp : ℕ → ℝ) (Ph : ℕ → Fin n → ℝ) (K : Fin n → ℝ) (Km : ℝ)

private lemma L_le_Tpipe (i : Fin n) : N.L i ≤ N.Tpipe :=
  le_trans (Finset.le_sup (f := N.L) (Finset.mem_univ i)) (le_max_right _ _)

private lemma post_eq (s S p : ℝ) (hsS : s ≤ S) :
    p + (if 0 < (if p ≤ s then S - p else 0) then (if p ≤ s then S - p else 0) else 0)
      = if p ≤ s then S else p := by
  split_ifs with h1 h2 <;> linarith

private lemma req_ind (K s S p : ℝ) :
    (if 0 < (if p ≤ s then S - p else 0) then K else 0) = K * (if p ≤ s ∧ p < S then 1 else 0) := by
  by_cases h1 : p ≤ s
  · by_cases h2 : p < S
    · rw [if_pos h1, if_pos (by linarith), if_pos ⟨h1, h2⟩, mul_one]
    · rw [if_pos h1, if_neg (by linarith), if_neg (fun h => h2 h.2), mul_zero]
  · rw [if_neg h1, if_neg (lt_irrefl 0), if_neg (fun h => h1 h.1), mul_zero]

/-- Prepared periods: no stock is in transit to a retailer once the pipelines have arrived. -/
private lemma prep_receive_I (t : ℕ) (hI : RInv N x c d act Yp Ph K Km t)
    (hrun : (fifoRun N x c d t).running = false) (hT : N.Tpipe ≤ t + 1) (i : Fin n) :
    (receive (fifoRun N x c d t) t).I i = BB N x i - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) := by
  have hpre := hI.prep hrun
  have hphys := physPos_eq N x c d (receive (fifoRun N x c d t) t) t i
    (by show (fifoRun N x c d t).I i + (fifoRun N x c d t).retPipe i t = _
        rw [hI.inv i, hI.rp i t le_rfl])
    (fun t' ht' => hI.rp i t' (by omega))
  have hsum0 : ∑ r ∈ Finset.range t, dispE N x c d r i = 0 :=
    Finset.sum_eq_zero fun r hr => (hpre r (Finset.mem_range.1 hr)).2 i
  have htr : inTransit N.L (receive (fifoRun N x c d t) t) t i = 0 := by
    unfold inTransit
    refine Finset.sum_eq_zero fun k hk => ?_
    show (fifoRun N x c d t).retPipe i (t + 1 + k) = 0
    rw [hI.rp i _ (by omega)]
    split_ifs with h
    · have hL := L_le_Tpipe N i
      unfold retArrE
      rw [if_neg (by omega)]
      exact (hpre _ (by omega)).2 i
    · rfl
  unfold physPos at hphys
  rw [htr, add_zero, hsum0, add_zero] at hphys
  exact hphys

variable (hK : ∀ i, 0 ≤ K i) (hKm : ∀ i, K i ≤ Km) (hKm0 : 0 ≤ Km)
  (hx : x.Valid) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : c.s0 ≤ c.S0)
  (hact : ∀ t, act t ↔ (N.Tpipe ≤ t + 1 ∧ ∀ i, x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
  (hY0 : Yp 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i))
  (hY : ∀ t, Yp (t + 1) = (if act t ∧ Yp t ≤ c.s0 then c.S0 else Yp t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ))
  (hPh0 : ∀ i, Ph 0 i = if act 0 then c.S i else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s)
  (hPh : ∀ t i, Ph (t + 1) i = if act (t + 1) then
        (if act t then (if Ph t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i
          else Ph t i - ((d t i : ℝ≥0) : ℝ)) else c.S i)
      else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        - ∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ))

include hK hKm hKm0 hx hsS hs0 hact hY0 hY hPh in
/-- Case A: a running period. -/
private lemma step_A (t : ℕ) (hI : RInv N x c d act Yp Ph K Km t)
    (hrun : (fifoRun N x c d t).running = true) : RInv N x c d act Yp Ph K Km (t + 1) := by
  obtain ⟨ht0, hact'⟩ := hI.run.1 hrun
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [add_tsub_cancel_right] at hact'
  have hactt : act (t' + 1) := act_mono N x c d act hact t' hact'
  set st0 := fifoRun N x c d (t' + 1) with hst0
  set st := receive st0 (t' + 1) with hstdef
  have hG : ∀ r ∈ st.queue, Good r := fun r hr => (hI.good r hr).1
  have hphys : ∀ i, physPos N.L st (t' + 1) i = BB N x i
      + ∑ r ∈ Finset.range (t' + 1), dispE N x c d r i
      - ∑ r ∈ Finset.range (t' + 1), ((d r i : ℝ≥0) : ℝ) := fun i =>
    physPos_eq N x c d st (t' + 1) i
      (by show st0.I i + st0.retPipe i (t' + 1) = _; rw [hI.inv i, hI.rp i _ le_rfl])
      (fun t'' ht'' => hI.rp i t'' (by omega))
  have hphat : ∀ i, phat N.L st (t' + 1) i = Ph t' i - ((d t' i : ℝ≥0) : ℝ) := by
    intro i
    unfold phat
    rw [hphys i, reserve_zero st hG, hI.ph t' rfl hact' i]
    show _ = retPosE N x c d i t' + uL st0.queue i - _
    unfold retPosE
    rw [Finset.sum_range_succ (fun r => ((d r i : ℝ≥0) : ℝ))]
    have hq : st.queue = st0.queue := rfl
    simp only [unalloc, hq]
    unfold uL
    ring
  have hreq : ∀ i, reqSize N.L c.params st (t' + 1) i
      = if Ph t' i - ((d t' i : ℝ≥0) : ℝ) ≤ c.s i then c.S i - (Ph t' i - ((d t' i : ℝ≥0) : ℝ))
        else 0 := fun i => by
    unfold reqSize; rw [hphat i]; rfl
  refine step_running N x c d act Yp Ph K Km hK hKm hKm0 hx hs0 hY0 hY (t' + 1) hI st
    (fifoStep_run N c (t' + 1) st0 hrun) rfl (fun i => rfl) rfl rfl hrun hG hI.head hactt
    (fun ⟨r, hr, _⟩ => hI.fifo (List.ne_nil_of_mem hr)) ?_ ?_
  · -- the request positions
    intro i
    rw [hPh t' i, if_pos hactt, if_pos hact']
    unfold QnE
    rw [uL_append, uL_newL, hreq i]
    have e1 := hI.ph t' rfl hact' i
    have e2 : retPosE N x c d i (t' + 1) = retPosE N x c d i t' + dispE N x c d (t' + 1) i
        - ((d t' i : ℝ≥0) : ℝ) := by
      unfold retPosE
      rw [Finset.sum_range_succ (fun r => dispE N x c d r i) (t' + 1),
        Finset.sum_range_succ (fun r => ((d r i : ℝ≥0) : ℝ)) t']
      ring
    have e3 := post_eq (c.s i) (c.S i) (Ph t' i - ((d t' i : ℝ≥0) : ℝ)) (hsS i)
    show _ = _ + (uL st0.queue i + _ - _)
    rw [e2, ← e3]
    linarith
  · -- Lemma 7
    have hl7 := hI.l7
    rw [hrun] at hl7
    simp only [if_true, mul_one] at hl7
    unfold QnE
    rw [zK_append, zK_newL]
    have hReq : ReqE c d act Ph K (t' + 1)
        = ∑ i, (if 0 < reqSize N.L c.params st (t' + 1) i then K i else 0) := by
      unfold ReqE
      rw [if_pos ⟨by omega, by simpa using hact'⟩]
      simp only [add_tsub_cancel_right]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hreq i, req_ind]
    rw [Finset.sum_range_succ (ReqE c d act Ph K), hReq,
      Finset.sum_range_succ (fun r => if 0 < supArrE N x c d r then (1 : ℝ) else 0)]
    have hq : zK K st.queue = zK K (fifoRun N x c d (t' + 1)).queue := rfl
    rw [hq]
    linarith

include hK in
private lemma ReqE_nonneg (r : ℕ) : 0 ≤ ReqE c d act Ph K r := by
  unfold ReqE
  split_ifs
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hK i) (by split_ifs <;> norm_num)
  · exact le_rfl

include hK hKm hKm0 hx hsS hs0 hact hY0 hY hPh0 hPh in
/-- Case B: the period in which the policy starts. -/
private lemma step_B (t : ℕ) (hI : RInv N x c d act Yp Ph K Km t)
    (hrun : (fifoRun N x c d t).running = false)
    (hc : N.Tpipe ≤ t + 1 ∧ ∀ i, (receive (fifoRun N x c d t) t).I i ≤ c.S i) :
    RInv N x c d act Yp Ph K Km (t + 1) := by
  set st0 := fifoRun N x c d t with hst0
  set I0 : Fin n → ℝ := fun i => (receive st0 t).I i with hI0
  set st := startWith (receive st0 t) t (fun i => c.S i - I0 i) (fun _ => 0) with hstdef
  have hpre := hI.prep hrun
  have hemp : st0.queue = [] := hI.emp hrun
  have hI0e : ∀ i, I0 i = BB N x i - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) :=
    fun i => prep_receive_I N x c d act Yp Ph K Km t hI hrun hc.1 i
  have hactt : act t := by
    rw [hact]
    refine ⟨hc.1, fun i => ?_⟩
    have := hc.2 i
    have e := hI0e i
    simp only [hI0] at e
    unfold BB at e
    linarith
  have hq : st.queue = newL (fun i => c.S i - I0 i) (fun _ => 0) t := by
    show st0.queue ++ _ = _
    rw [hemp, List.nil_append]
    rfl
  have hG : ∀ r ∈ st.queue, Good r := by rw [hq]; exact newL_good
  have h0 : ∀ r ∈ st.queue, r.alloc = 0 := fun r hr => by rw [hq] at hr; exact (newL_mem hr).1
  have hsum0 : ∀ i, ∑ r ∈ Finset.range t, dispE N x c d r i = 0 := fun i =>
    Finset.sum_eq_zero fun r hr => (hpre r (Finset.mem_range.1 hr)).2 i
  have hphys : ∀ i, physPos N.L st t i = I0 i := by
    intro i
    have := physPos_eq N x c d st t i
      (by show st0.I i + st0.retPipe i t = _; rw [hI.inv i, hI.rp i _ le_rfl])
      (fun t'' ht'' => hI.rp i t'' (by omega))
    rw [this, hsum0, add_zero, hI0e]
  have huq : ∀ i, uL st.queue i = c.S i - I0 i := by
    intro i
    rw [hq, uL_newL]
    split_ifs with h
    · rfl
    · have := hc.2 i; simp only [hI0] at *; linarith
  have hphat : ∀ i, phat N.L st t i = c.S i := by
    intro i
    unfold phat
    rw [hphys i, reserve_zero st hG]
    show I0 i + uL st.queue i + 0 = c.S i
    rw [huq i]; ring
  have hreq : ∀ i, reqSize N.L c.params st t i = 0 := by
    intro i
    unfold reqSize
    rw [hphat i]
    split_ifs <;> simp [FIFOChoice.params]
  refine step_running N x c d act Yp Ph K Km hK hKm hKm0 hx hs0 hY0 hY t hI st
    (fifoStep_start N c t st0 hrun hc) rfl (fun i => rfl) rfl rfl rfl hG
    (fun r hr => h0 r (List.mem_of_mem_tail hr)) hactt
    (fun ⟨r, hr, hra⟩ => absurd (h0 r hr) hra.ne') ?_ ?_
  · -- the request positions
    intro i
    have hPt : Ph t i = c.S i := by
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht; rw [hPh0 i, if_pos hactt]
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        have hna : ¬ act t' := fun h => by
          have := hI.run.2 ⟨by omega, by simpa using h⟩
          rw [hrun] at this; exact absurd this (by simp)
        rw [hPh t' i, if_pos hactt, if_neg hna]
    rw [hPt]
    unfold QnE
    rw [uL_append, uL_newL, hreq i, if_neg (lt_irrefl 0), add_zero, huq i]
    unfold retPosE
    rw [Finset.sum_range_succ, hsum0, zero_add, hI0e]
    ring
  · -- Lemma 7
    have hz0 : ∑ r ∈ Finset.range t, ∑ i, K i * (if 0 < dispE N x c d r i then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun i _ => by
        rw [(hpre r (Finset.mem_range.1 hr)).2 i]; simp
    unfold QnE
    rw [hz0, zK_append, zK_newL, hq, zK_newL]
    have h1 : ∑ i, (if 0 < reqSize N.L c.params st t i then K i else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hreq i, if_neg (lt_irrefl 0)]
    have h2 : ∑ i, (if 0 < c.S i - I0 i then K i else 0) ≤ (n : ℝ) * Km := by
      calc ∑ i, (if 0 < c.S i - I0 i then K i else 0) ≤ ∑ _i : Fin n, Km :=
            Finset.sum_le_sum fun i _ => by split_ifs; exacts [hKm i, hKm0]
        _ = (n : ℝ) * Km := by simp
    have h3 : 0 ≤ ∑ r ∈ Finset.range (t + 1), ReqE c d act Ph K r :=
      Finset.sum_nonneg fun r _ => ReqE_nonneg c d act Ph K hK r
    have h4 : (if 0 < supArrE N x c d t then (1 : ℝ) else 0)
        ≤ ∑ r ∈ Finset.range (t + 1), (if 0 < supArrE N x c d r then 1 else 0) := by
      rw [Finset.sum_range_succ]
      have : 0 ≤ ∑ r ∈ Finset.range t, (if 0 < supArrE N x c d r then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun r _ => by split_ifs <;> norm_num
      linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hKm0
    nlinarith

include hK hKm0 hx hact in
/-- Case C: a preparation period. -/
private lemma step_C (t : ℕ) (hI : RInv N x c d act Yp Ph K Km t)
    (hrun : (fifoRun N x c d t).running = false)
    (hc : ¬ (N.Tpipe ≤ t + 1 ∧ ∀ i, (receive (fifoRun N x c d t) t).I i ≤ c.S i)) :
    RInv N x c d act Yp Ph K Km (t + 1) := by
  set st0 := fifoRun N x c d t with hst0
  have hfs := fifoStep_prep N c t st0 hrun hc
  have hpre := hI.prep hrun
  have hemp : st0.queue = [] := hI.emp hrun
  have e_ord : ordE N x c d t = 0 := by unfold ordE; rw [hfs]
  have e_disp : ∀ i, dispE N x c d t i = 0 := fun i => by unfold dispE; rw [hfs]; rfl
  have hR1 : fifoRun N x c d (t + 1) = applyDemand (receive st0 t) (d t) := by rw [run_succ, hfs]
  have hnact : ¬ act t := by
    intro h
    rw [hact] at h
    apply hc
    refine ⟨h.1, fun i => ?_⟩
    rw [prep_receive_I N x c d act Yp Ph K Km t hI hrun h.1 i]
    unfold BB
    exact h.2 i
  have f_run : (fifoRun N x c d (t + 1)).running = false := by rw [hR1]; exact hrun
  have f_wb : (fifoRun N x c d (t + 1)).Wbar = st0.Wbar + st0.supPipe t := by rw [hR1]; rfl
  have f_q : (fifoRun N x c d (t + 1)).queue = [] := by rw [hR1]; exact hemp
  have hsa0 : 0 ≤ supArrE N x c d t := by
    unfold supArrE
    split_ifs with h
    · exact hx.2.1 t
    · rcases Nat.lt_or_ge (t - N.L0) t with h' | h'
      · rw [(hpre _ h').1]
      · rw [show t - N.L0 = t by omega, e_ord]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f_run]; simp only [Bool.false_eq_true, false_iff, not_and]; intro _; simpa using hnact
  · rw [f_wb, Finset.sum_range_succ, hI.sp t le_rfl]
    have h1 : st0.Wbar = x.W + ∑ r ∈ Finset.range t, (supArrE N x c d r - ∑ i, dispE N x c d r i) :=
      hI.wbar
    simp only [e_disp, Finset.sum_const_zero, sub_zero]
    by_cases hL : N.L0 = 0
    · rw [if_neg (by omega)]
      have : supArrE N x c d t = 0 := by simp [supArrE, hL, e_ord]
      rw [this]; linarith
    · rw [if_pos (by omega)]; linarith
  · intro t' ht'
    have : (fifoRun N x c d (t + 1)).supPipe = st0.supPipe := by rw [hR1]; rfl
    rw [this, hI.sp t' (by omega)]
    by_cases he : t' = t + N.L0
    · subst he
      rw [if_neg (by omega)]
      have : supArrE N x c d (t + N.L0) = 0 := by simp [supArrE, e_ord]
      rw [this]; split_ifs <;> rfl
    · by_cases h1 : t' < t + N.L0
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
  · intro i
    have : (fifoRun N x c d (t + 1)).I i = st0.I i + st0.retPipe i t - ((d t i : ℝ≥0) : ℝ) := by
      rw [hR1]; rfl
    rw [this, Finset.sum_range_succ, hI.rp i t le_rfl]
    have h1 : st0.I i = x.I i + ∑ r ∈ Finset.range t, (retArrE N x c d i r - ((d r i : ℝ≥0) : ℝ)) :=
      hI.inv i
    by_cases hL : N.L i = 0
    · rw [if_neg (by omega)]
      have : retArrE N x c d i t = 0 := by simp [retArrE, hL, e_disp]
      rw [this]; linarith
    · rw [if_pos (by omega)]; linarith
  · intro i t' ht'
    have : (fifoRun N x c d (t + 1)).retPipe i = st0.retPipe i := by rw [hR1]; rfl
    rw [this, hI.rp i t' (by omega)]
    by_cases he : t' = t + N.L i
    · subst he
      rw [if_neg (by omega)]
      have : retArrE N x c d i (t + N.L i) = 0 := by simp [retArrE, e_disp]
      rw [this]; split_ifs <;> rfl
    · by_cases h1 : t' < t + N.L i
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
  · rw [f_q]; simp
  · rw [f_q]; simp
  · rw [f_q]; simp
  · rw [f_wb, hI.sp t le_rfl]
    have := hI.wnn
    split_ifs <;> linarith
  · intro _; exact f_q
  · intro _ r hr
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with h | h
    · exact hpre r h
    · subst h; exact ⟨e_ord, e_disp⟩
  · intro r hr
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with h | h
    · exact hI.ord r h
    · subst h; rw [e_ord, if_neg (fun h => hnact h.1)]
  · intro t' ht' ha
    have : t' = t := by omega
    rw [this] at ha
    exact absurd ha hnact
  · have hl7 := hI.l7
    rw [f_q, f_run, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [hemp, hrun] at hl7
    simp only [e_disp, lt_irrefl, if_false, mul_zero, Finset.sum_const_zero, add_zero,
      Bool.false_eq_true] at hl7 ⊢
    have h3 : 0 ≤ ReqE c d act Ph K t := ReqE_nonneg c d act Ph K hK t
    have h4 : 0 ≤ Km * (if 0 < supArrE N x c d t then (1 : ℝ) else 0) :=
      mul_nonneg hKm0 (by split_ifs <;> norm_num)
    nlinarith
  · intro r hr i
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with h | h
    · exact hI.dnn r h i
    · subst h; rw [e_disp i]

include hK hKm hKm0 hx hsS hs0 hact hY0 hY hPh0 hPh in
private lemma rinv_all : ∀ t, RInv N x c d act Yp Ph K Km t
  | 0 => rinv_zero N x c d act Yp Ph K Km hx
  | t + 1 => by
    have hI := rinv_all t
    by_cases hrun : (fifoRun N x c d t).running = true
    · exact step_A N x c d act Yp Ph K Km hK hKm hKm0 hx hsS hs0 hact hY0 hY hPh t hI hrun
    · have hrun' : (fifoRun N x c d t).running = false := by simpa using hrun
      by_cases hc : N.Tpipe ≤ t + 1 ∧ ∀ i, (receive (fifoRun N x c d t) t).I i ≤ c.S i
      · exact step_B N x c d act Yp Ph K Km hK hKm hKm0 hx hsS hs0 hact hY0 hY hPh0 hPh t hI hrun' hc
      · exact step_C N x c d act Yp Ph K Km hK hKm0 hx hact t hI hrun' hc

end cases

private lemma sum_ind_le_card (T : ℕ) (g : ℕ → ℝ) (hg : ∀ t, g t ≤ 1) :
    ∑ t ∈ Finset.range T, g t ≤ T := by
  calc ∑ t ∈ Finset.range T, g t ≤ ∑ _t ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t _ => hg t
    _ = T := by simp

section feas

variable {n : ℕ} (N : Network n) (x : InitState n) (c : FIFOChoice n)

/-- The start condition of `π_FIFO` (Appendix B, Step 1). -/
private def actF (d : ℕ → DemandVec n) (t : ℕ) : Prop :=
  N.Tpipe ≤ t + 1 ∧ ∀ i, x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
    - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i

private noncomputable instance actF_dec (d : ℕ → DemandVec n) : DecidablePred (actF N x c d) :=
  fun t => by unfold actF; infer_instance

/-- The supplier echelon position before the order of period `t`. -/
private noncomputable def YpF (d : ℕ → DemandVec n) : ℕ → ℝ
  | 0 => x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i)
  | t + 1 => (if actF N x c d t ∧ YpF d t ≤ c.s0 then c.S0 else YpF d t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ)

/-- Retailer request positions after the requests of period `t`. -/
private noncomputable def PhF (d : ℕ → DemandVec n) : ℕ → Fin n → ℝ
  | 0 => fun i => if actF N x c d 0 then c.S i
      else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
  | t + 1 => fun i => if actF N x c d (t + 1) then
      (if actF N x c d t then (if PhF d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i
        else PhF d t i - ((d t i : ℝ≥0) : ℝ)) else c.S i)
      else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        - ∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ)

/-- The state at the start of period `t` depends only on the demands of periods before `t`. -/
private lemma run_dep (d d' : ℕ → DemandVec n) : ∀ t, (∀ s < t, d s = d' s) →
    fifoRun N x c d t = fifoRun N x c d' t
  | 0, _ => rfl
  | t + 1, h => by
    show applyDemand (fifoStep N c t (fifoRun N x c d t)).1 (d t)
      = applyDemand (fifoStep N c t (fifoRun N x c d' t)).1 (d' t)
    rw [run_dep d d' t (fun s hs => h s (by omega)), h t (by omega)]

end feas

/-- `π_FIFO` (for any choices with `sᵢ ≤ Sᵢ` and `s₀ ≤ S₀`) is nonanticipative and feasible:
orders and dispatches are nonnegative and the dispatches never exceed the available warehouse
stock. -/
theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (x : InitState n) (hx : x.Valid)
    (c : FIFOChoice n) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : c.s0 ≤ c.S0) :
    (fifoPolicy N x c).toPolicy.Nonanticipative ∧ (fifoPolicy N x c).toPolicy.Feasible N x := by
  have hK := hN.K_nonneg
  have hKm : ∀ i, N.K i ≤ N.Kmax := fun i => le_ciSup (Set.finite_range _).bddAbove i
  have hKm0 : 0 ≤ N.Kmax := by
    rcases isEmpty_or_nonempty (Fin n) with h | h
    · simp [Network.Kmax, Real.iSup_of_isEmpty]
    · obtain ⟨i⟩ := h; exact le_trans (hK i) (hKm i)
  refine ⟨fun t u d d' h => ?_, fun u d t => ?_⟩
  · have e := run_dep N x c d d' t h
    refine ⟨?_, ?_⟩
    · show (fifoStep N c t (fifoRun N x c d t)).2.1 = (fifoStep N c t (fifoRun N x c d' t)).2.1
      rw [e]
    · show (fifoStep N c t (fifoRun N x c d t)).2.2 = (fifoStep N c t (fifoRun N x c d' t)).2.2
      rw [e]
  · have hall := rinv_all N x c d (actF N x c d) (YpF N x c d) (PhF N x c d) N.K N.Kmax hK hKm
      hKm0 hx hsS hs0 (fun t => Iff.rfl) rfl (fun t => rfl) (fun i => rfl) (fun t i => rfl)
    have hI := hall (t + 1)
    have ho : (fifoPolicy N x c).toPolicy.order t u d = ordE N x c d t := rfl
    have hd : ∀ i, (fifoPolicy N x c).toPolicy.dispatch t u d i = dispE N x c d t i := fun i => rfl
    have hws : Policy.whStock N x (fifoPolicy N x c).toPolicy u d t
        = (fifoRun N x c d (t + 1)).Wbar := hI.wbar.symm
    have hav : Policy.whAvailable N x (fifoPolicy N x c).toPolicy u d t
        = Policy.whStock N x (fifoPolicy N x c).toPolicy u d t
          + ∑ i, (fifoPolicy N x c).toPolicy.dispatch t u d i := by
      unfold Policy.whAvailable Policy.whStock
      rw [Finset.sum_range_succ]
      ring
    refine ⟨?_, fun i => ?_, ?_⟩
    · rw [ho, hI.ord t (by omega)]
      split_ifs with h
      · linarith [h.2]
      · exact le_rfl
    · rw [hd i]; exact hI.dnn t (by omega) i
    · rw [hav, hws]
      linarith [hI.wnn]
