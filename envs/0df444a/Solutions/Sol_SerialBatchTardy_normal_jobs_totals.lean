-- Prove2me | solution 1 for SerialBatchTardy.normal_jobs_totals
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:09:40.644717+00:00
-- url     : https://prove2.me/submissions/030a5cf8-775f-4005-b450-c56e92477a2c

import Mathlib
import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace SerialBatchTardy.Aux_SB

open SerialBatchTardy

theorem sum_map_flatMap {α β : Type} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_ite_nodup {β : Type} [DecidableEq β] (l : List β) (hl : l.Nodup) (e : β)
    (he : e ∈ l) (c : ℕ) : (l.map fun y => if y = e then c else 0).sum = c := by
  induction l with
  | nil => simp at he
  | cons y l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons]
    by_cases hye : y = e
    · subst hye
      rw [if_pos rfl]
      have : (l.map fun y' => if y' = y then c else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro z hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        rw [if_neg (fun (h : w = y) => hl.1 (h ▸ hw))]
      rw [this, add_zero]
    · rw [if_neg hye, zero_add]
      have he' : e ∈ l := by
        rcases List.mem_cons.mp he with h | h
        · exact absurd h.symm hye
        · exact h
      exact ih hl.2 he'

theorem digits_sum (b : ℕ) (ds : List ℕ) :
    ((List.range ds.length).map fun h => ds.getD h 0 * b ^ h).sum = Nat.ofDigits b ds := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
      Nat.ofDigits_cons, ← ih]
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one,
      pow_succ]
    congr 1
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro h _
    ring

theorem gadget_sum (xs : List ℕ) (ℓ x : ℕ) (g : JobLabel → ℕ) :
    ((gadgetLabels xs ℓ x).map g).sum =
      ((List.range (Nat.digits xs.length x).length).map fun h =>
        (Nat.digits xs.length x).getD h 0 * g (JobLabel.normal ℓ x h)).sum := by
  unfold gadgetLabels
  rw [sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro h _
  simp

theorem filter_sum (xs : List ℕ) (k : ℕ) (L : List ℕ) (hnd : xs.Nodup) (x : ℕ)
    (hx : x ∈ xs) (ℓ : ℕ) (hℓ : ℓ < k) (g : JobLabel → ℕ) :
    ((hardLabels xs k L).map fun a =>
        if a.gadget? = some ℓ ∧ a.value? = some x then g a else 0).sum =
      ((gadgetLabels xs ℓ x).map g).sum := by
  set G := ((gadgetLabels xs ℓ x).map g).sum with hG
  have hgad : ∀ ℓ' x', ((gadgetLabels xs ℓ' x').map fun a =>
      if a.gadget? = some ℓ ∧ a.value? = some x then g a else 0).sum =
      if ℓ' = ℓ then (if x' = x then G else 0) else 0 := by
    intro ℓ' x'
    have hmem : ∀ a ∈ gadgetLabels xs ℓ' x', ∃ h, a = JobLabel.normal ℓ' x' h := by
      intro a ha
      unfold gadgetLabels at ha
      obtain ⟨h, _, hh⟩ := List.mem_flatMap.mp ha
      exact ⟨h, List.eq_of_mem_replicate hh⟩
    by_cases h1 : ℓ' = ℓ
    · by_cases h2 : x' = x
      · subst h1; subst h2
        rw [if_pos rfl, if_pos rfl, hG]
        congr 1
        apply List.map_congr_left
        intro a ha
        obtain ⟨h, rfl⟩ := hmem a ha
        simp [JobLabel.gadget?, JobLabel.value?]
      · rw [if_pos h1, if_neg h2]
        apply List.sum_eq_zero
        intro z hz
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
        obtain ⟨h, rfl⟩ := hmem a ha
        simp [JobLabel.gadget?, JobLabel.value?, h2]
    · rw [if_neg h1]
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      obtain ⟨h, rfl⟩ := hmem a ha
      simp [JobLabel.gadget?, JobLabel.value?, h1]
  unfold hardLabels
  rw [List.map_append, List.sum_append]
  have hleft : ((L.map JobLabel.leftover).map fun a =>
      if a.gadget? = some ℓ ∧ a.value? = some x then g a else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro z hz
    simp only [List.map_map, List.mem_map, Function.comp_apply] at hz
    obtain ⟨e, _, rfl⟩ := hz
    simp [JobLabel.gadget?]
  rw [hleft, zero_add, sum_map_flatMap]
  simp only [sum_map_flatMap, hgad]
  have hinner : ∀ ℓ', (xs.map fun x' => if ℓ' = ℓ then (if x' = x then G else 0) else 0).sum =
      if ℓ' = ℓ then G else 0 := by
    intro ℓ'
    by_cases h1 : ℓ' = ℓ
    · simp only [if_pos h1]
      exact sum_ite_nodup xs hnd x hx G
    · simp [h1]
  simp only [hinner]
  exact sum_ite_nodup (List.range k) List.nodup_range ℓ (List.mem_range.mpr hℓ) G

theorem fin_sum (xs : List ℕ) (t k : ℕ) (L : List ℕ) (ℓ x : ℕ) (f : Job → ℕ) :
    ∑ j ∈ gadgetSet xs t k L ℓ x, f ((hardInstance xs t k L).job j) =
      ((hardLabels xs k L).map fun a =>
        if a.gadget? = some ℓ ∧ a.value? = some x then f (labelJob xs t k a) else 0).sum := by
  classical
  have hlen : (hardInstance xs t k L).jobs.length = (hardLabels xs k L).length := by
    simp [hardInstance]
  unfold gadgetSet
  rw [Finset.sum_filter]
  rw [← Fin.sum_univ_fun_getElem]
  rw [← Equiv.sum_comp (finCongr hlen.symm)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [labelOf, Instance.job, hardInstance, List.get_eq_getElem, List.getElem_map]
  rfl

end SerialBatchTardy.Aux_SB

open SerialBatchTardy SerialBatchTardy.Aux_SB in
theorem solution (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup) (x : ℕ)
    (hx : x ∈ xs) (ℓ : ℕ) (hℓ : ℓ < k) :
    pSum (gadgetSet xs t k L ℓ x) = x ∧ wSum (gadgetSet xs t k L ℓ x) = xs.prod * (x + 1) := by
  have hds := digits_sum xs.length (Nat.digits xs.length x)
  rw [Nat.ofDigits_digits] at hds
  constructor
  · unfold pSum
    rw [fin_sum xs t k L ℓ x Job.p, filter_sum xs k L hnd x hx ℓ hℓ, gadget_sum]
    simpa [labelJob] using hds
  · unfold wSum
    rw [fin_sum xs t k L ℓ x Job.w, filter_sum xs k L hnd x hx ℓ hℓ, gadget_sum]
    simp only [labelJob]
    have : ((List.range (Nat.digits xs.length x).length).map fun h =>
        (Nat.digits xs.length x).getD h 0 *
          (xs.length ^ h * (xs.prod + xs.prod / x))).sum =
        ((List.range (Nat.digits xs.length x).length).map fun h =>
          (Nat.digits xs.length x).getD h 0 * xs.length ^ h).sum * (xs.prod + xs.prod / x) := by
      rw [← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro h _
      ring
    rw [this, hds, mul_add, Nat.mul_div_cancel' (List.dvd_prod hx)]
    ring
