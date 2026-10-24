-- Prove2me | solution 1 for SkutellaCQP.Preempt.power_of_preemption
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T08:46:35.857486+00:00
-- url     : https://prove2.me/submissions/923820b0-342e-4a13-9ef0-d45d5c372920

import Mathlib
import Definitions.Def_SkutellaCQP_Preempt_Setting

noncomputable section
open Finset SkutellaCQP.Preempt
namespace PreemptionProof
variable {m n : ℕ}

def duration (P : PSched m n) (i : Fin m) (j : Fin n) : ℝ :=
  ∑ q : Fin P.length, if (P.get q).mach = i ∧ (P.get q).job = j then
    (P.get q).stop - (P.get q).start else 0

def fraction (p : Fin m → Fin n → ℝ) (P : PSched m n) (i : Fin m) (j : Fin n) : ℝ :=
  duration P i j / p i j

def weight (a : Fin m → Fin n → ℝ) (σ : Fin n → Fin m) : ℝ := ∏ j, a (σ j) j

def earlierLoad (p : Fin m → Fin n → ℝ) (P : PSched m n)
    (σ : Fin n → Fin m) (j : Fin n) : ℝ :=
  ∑ k ∈ univ.filter (fun k => cprec P k j ∧ σ k = σ j), p (σ j) k

def rounded (p : Fin m → Fin n → ℝ) (P : PSched m n)
    (κ : ℝ) (σ : Fin n → Fin m) : PSched m n :=
  List.ofFn (fun j : Fin n => ({job := j, mach := σ j, start := κ * pcompl P j + earlierLoad p P σ j, stop := κ * pcompl P j + earlierLoad p P σ j + p (σ j) j} : Piece m n))
end PreemptionProof

noncomputable section
open Finset
namespace PreemptionProof

theorem interval_packing {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (start stop : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hstart : ∀ q ∈ s, 0 ≤ start q)
    (hlen : ∀ q ∈ s, start q ≤ stop q)
    (hstop : ∀ q ∈ s, stop q ≤ C)
    (hdis : ∀ q ∈ s, ∀ q' ∈ s, q ≠ q' → stop q ≤ start q' ∨ stop q' ≤ start q) :
    ∑ q ∈ s, (stop q - start q) ≤ C := by
  induction s using Finset.strongInductionOn generalizing C with
  | _ s ih =>
    by_cases hz : ∃ q ∈ s, start q = stop q
    · obtain ⟨q, hq, heq⟩ := hz
      have hi := ih (s.erase q) (Finset.erase_ssubset hq) C hC
        (fun x hx => hstart x (mem_of_mem_erase hx))
        (fun x hx => hlen x (mem_of_mem_erase hx))
        (fun x hx => hstop x (mem_of_mem_erase hx))
        (fun x hx y hy hxy => hdis x (mem_of_mem_erase hx) y (mem_of_mem_erase hy) hxy)
      rw [← Finset.sum_erase_add _ _ hq]
      simpa only [heq, sub_self, add_zero] using hi
    · by_cases hs : s.Nonempty
      · obtain ⟨q, hq, hmax⟩ := s.exists_max_image start hs
        have hqpos : start q < stop q := lt_of_le_of_ne (hlen q hq) (by
          intro he; exact hz ⟨q, hq, he⟩)
        have hbefore : ∀ x ∈ s.erase q, stop x ≤ start q := by
          intro x hx
          rcases hdis x (mem_of_mem_erase hx) q hq (ne_of_mem_erase hx) with h | h
          · exact h
          · exact False.elim ((not_lt_of_ge (h.trans (hmax x (mem_of_mem_erase hx)))) hqpos)
        have hi := ih (s.erase q) (Finset.erase_ssubset hq) (start q) (hstart q hq)
          (fun x hx => hstart x (mem_of_mem_erase hx))
          (fun x hx => hlen x (mem_of_mem_erase hx)) hbefore
          (fun x hx y hy hxy => hdis x (mem_of_mem_erase hx) y (mem_of_mem_erase hy) hxy)
        rw [← Finset.sum_erase_add _ _ hq]
        linarith [hstop q hq]
      · simpa only [Finset.not_nonempty_iff_eq_empty.mp hs, sum_empty] using hC
end PreemptionProof

noncomputable section
open Finset SkutellaCQP.Preempt
namespace PreemptionProof
variable {m n : ℕ}

theorem indexed_filter_sum {α : Type*} (l : List α) (b : α → Bool) (f : α → ℝ) :
    ((l.filter b).map f).sum = ∑ q : Fin l.length, if b (l.get q) then f (l.get q) else 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.filter_cons, Fin.sum_univ_succ]; split <;> simp_all

theorem maxfold_nonneg (l : List ℝ) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => exact ih.trans (le_max_right _ _)

theorem le_maxfold {l : List ℝ} {x : ℝ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

theorem completion_nonneg (P : PSched m n) (j : Fin n) : 0 ≤ pcompl P j :=
  maxfold_nonneg _

theorem piece_stop_le (P : PSched m n) (q : Fin P.length) :
    (P.get q).stop ≤ pcompl P (P.get q).job := by
  apply le_maxfold
  apply List.mem_map.mpr
  exact ⟨P.get q, List.mem_filter.mpr ⟨List.get_mem _ _, by simp⟩, rfl⟩

theorem piece_nonneg (p r : Fin m → Fin n → ℝ) (P : PSched m n)
    (hr : ∀ i j, 0 ≤ r i j) (hP : PFeasible p r P) (q : Fin P.length) :
    0 ≤ (P.get q).start ∧ 0 ≤ ((P.get q).stop - (P.get q).start) := by
  have h := hP.1 (P.get q) (List.get_mem P q)
  exact ⟨(hr _ _).trans h.1, sub_nonneg.mpr h.2⟩

theorem duration_nonneg (p r : Fin m → Fin n → ℝ) (P : PSched m n)
    (hr : ∀ i j, 0 ≤ r i j) (hP : PFeasible p r P) (i : Fin m) (j : Fin n) :
    0 ≤ duration P i j := by
  apply sum_nonneg
  intro q _
  split
  · exact (piece_nonneg p r P hr hP q).2
  · exact le_rfl

theorem fraction_nonneg (p r : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (hr : ∀ i j, 0 ≤ r i j) (hP : PFeasible p r P)
    (i : Fin m) (j : Fin n) : 0 ≤ fraction p P i j :=
  div_nonneg (duration_nonneg p r P hr hP i j) (hp i j).le

theorem fraction_mul (p : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (i : Fin m) (j : Fin n) :
    fraction p P i j * p i j = duration P i j := by
  exact div_mul_cancel₀ _ (ne_of_gt (hp i j))

theorem fraction_sum_one (p r : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (hr : ∀ i j, 0 ≤ r i j) (hP : PFeasible p r P)
    (j : Fin n) : ∑ i, fraction p P i j = 1 := by
  have _ := hp
  have _ := hr
  rw [← hP.2.2.2 j, indexed_filter_sum]
  simp only [fraction, duration, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  by_cases hj : (P.get q).job = j
  · simp only [List.get_eq_getElem] at hj
    simp [hj, ite_div]
  · simp only [List.get_eq_getElem] at hj
    simp [hj]

theorem job_time_bound (p r : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (hr : ∀ i j, 0 ≤ r i j) (hP : PFeasible p r P)
    (j : Fin n) : ∑ i, fraction p P i j * p i j ≤ pcompl P j := by
  simp_rw [fraction_mul p P hp, duration]
  rw [sum_comm]
  have hid : (∑ q : Fin P.length, ∑ i : Fin m,
      if (P.get q).mach = i ∧ (P.get q).job = j then (P.get q).stop - (P.get q).start else 0) =
      ∑ q ∈ univ.filter (fun q : Fin P.length => (P.get q).job = j),
        ((P.get q).stop - (P.get q).start) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro q _
    by_cases hj : (P.get q).job = j
    · simp only [List.get_eq_getElem] at hj
      simp [hj]
    · simp only [List.get_eq_getElem] at hj
      simp [hj]
  rw [hid]
  apply interval_packing _ (fun q => (P.get q).start) (fun q => (P.get q).stop) _ (completion_nonneg P j)
  · intro q _; exact (piece_nonneg p r P hr hP q).1
  · intro q _; exact (hP.1 (P.get q) (List.get_mem P q)).2
  · intro q hq
    have hj := (mem_filter.mp hq).2
    simpa only [hj] using piece_stop_le P q
  · intro q hq q' hq' hne
    apply hP.2.2.1 q q' hne
    exact (mem_filter.mp hq).2.trans (mem_filter.mp hq').2.symm

theorem machine_prefix_bound (p r : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (hr : ∀ i j, 0 ≤ r i j) (hP : PFeasible p r P)
    (i : Fin m) (j : Fin n) :
    ∑ k ∈ univ.filter (fun k => cprec P k j), fraction p P i k * p i k ≤ pcompl P j := by
  simp_rw [fraction_mul p P hp, duration]
  rw [sum_comm]
  have hid : (∑ q : Fin P.length, ∑ k ∈ univ.filter (fun k => cprec P k j),
      if (P.get q).mach = i ∧ (P.get q).job = k then (P.get q).stop - (P.get q).start else 0) =
      ∑ q ∈ univ.filter (fun q : Fin P.length => (P.get q).mach = i ∧ cprec P (P.get q).job j),
        ((P.get q).stop - (P.get q).start) := by
    simp only [sum_filter]
    apply sum_congr rfl
    intro q _
    by_cases hi : (P.get q).mach = i
    · simp only [List.get_eq_getElem] at hi
      simp only [List.get_eq_getElem, hi, true_and]
      simp_rw [← ite_and, and_comm (a := cprec P _ j), ite_and]
      simp
    · simp only [List.get_eq_getElem] at hi
      simp [hi]
  rw [hid]
  apply interval_packing _ (fun q => (P.get q).start) (fun q => (P.get q).stop) _ (completion_nonneg P j)
  · intro q _; exact (piece_nonneg p r P hr hP q).1
  · intro q _; exact (hP.1 (P.get q) (List.get_mem P q)).2
  · intro q hq
    have hc := (mem_filter.mp hq).2.2
    exact (piece_stop_le P q).trans (hc.elim le_of_lt (fun h => h.1.le))
  · intro q hq q' hq' hne
    apply hP.2.1 q q' hne
    exact (mem_filter.mp hq).2.1.trans (mem_filter.mp hq').2.1.symm

theorem fraction_release (p r : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (hr : ∀ i j, 0 ≤ r i j) (hP : PFeasible p r P)
    (i : Fin m) (j : Fin n) (ha : 0 < fraction p P i j) : r i j ≤ pcompl P j := by
  have hd : 0 < duration P i j := (div_pos_iff_of_pos_right (hp i j)).mp ha
  obtain ⟨q, _, hq⟩ := (Finset.sum_pos_iff_of_nonneg (fun q _ => by
    split
    · exact (piece_nonneg p r P hr hP q).2
    · exact le_rfl)).mp hd
  split at hq
  next h =>
    have hh := hP.1 _ (List.get_mem P q)
    have hc := piece_stop_le P q
    simpa only [h.1, h.2] using hh.1.trans (hh.2.trans hc)
  next => exact False.elim (lt_irrefl _ hq)
end PreemptionProof

noncomputable section
open Finset SkutellaCQP.Preempt
namespace PreemptionProof
variable {m n : ℕ}

theorem weight_nonneg (a : Fin m → Fin n → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (σ : Fin n → Fin m) : 0 ≤ weight a σ := by
  exact Finset.prod_nonneg fun j _ => ha (σ j) j

theorem weight_sum (a : Fin m → Fin n → ℝ)
    (ha : ∀ j, ∑ i, a i j = 1) : ∑ σ : Fin n → Fin m, weight a σ = 1 := by
  classical
  unfold weight
  rw [← Fintype.prod_sum (fun j i => a i j)]
  simp only [ha, prod_const_one]

theorem weight_mul_prod (a : Fin m → Fin n → ℝ) (f : Fin n → Fin m → ℝ) :
    (∑ σ : Fin n → Fin m, weight a σ * ∏ j, f j (σ j)) =
      ∏ j, ∑ i, a i j * f j i := by
  classical
  simp_rw [weight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j i => a i j * f j i)).symm

theorem weight_marginal (a : Fin m → Fin n → ℝ)
    (ha : ∀ j, ∑ i, a i j = 1) (j : Fin n) (f : Fin m → ℝ) :
    ∑ σ : Fin n → Fin m, weight a σ * f (σ j) = ∑ i, a i j * f i := by
  classical
  have h := weight_mul_prod a (fun t i => if t = j then f i else 1)
  have hs (t : Fin n) :
      (∑ i, a i t * (if t = j then f i else 1)) =
        if t = j then ∑ i, a i j * f i else 1 := by
    by_cases ht : t = j
    · simp [ht]
    · simp [ht, ha]
  simp_rw [hs] at h
  simpa using h

theorem weight_product_marginal (a : Fin m → Fin n → ℝ)
    (ha : ∀ j, ∑ i, a i j = 1) (j k : Fin n) (hjk : j ≠ k)
    (f g : Fin m → ℝ) :
    (∑ σ : Fin n → Fin m, weight a σ * (f (σ j) * g (σ k))) =
      (∑ i, a i j * f i) * ∑ i, a i k * g i := by
  classical
  have h := weight_mul_prod a
    (fun t i => (if t = j then f i else 1) * (if t = k then g i else 1))
  have hs (t : Fin n) :
      (∑ i, a i t * ((if t = j then f i else 1) * (if t = k then g i else 1))) =
        (if t = j then ∑ i, a i j * f i else 1) *
          (if t = k then ∑ i, a i k * g i else 1) := by
    by_cases htj : t = j
    · subst t
      simp [hjk]
    · by_cases htk : t = k
      · subst t
        simp [Ne.symm hjk]
      · simp [htj, htk, ha]
  simp_rw [hs, Finset.prod_mul_distrib] at h
  simpa using h

theorem weight_pair (a : Fin m → Fin n → ℝ)
    (ha : ∀ j, ∑ i, a i j = 1) (j k : Fin n) (hjk : j ≠ k)
    (f : Fin m → Fin m → ℝ) :
    ∑ σ : Fin n → Fin m, weight a σ * f (σ j) (σ k) =
      ∑ i, ∑ h, a i j * a h k * f i h := by
  classical
  calc
    _ = ∑ σ : Fin n → Fin m, ∑ i : Fin m,
        weight a σ * ((if σ j = i then 1 else 0) * f i (σ k)) := by
      apply sum_congr rfl
      intro σ _
      simp
    _ = ∑ i : Fin m, ∑ σ : Fin n → Fin m,
        weight a σ * ((if σ j = i then 1 else 0) * f i (σ k)) := sum_comm
    _ = ∑ i, (∑ h, a h j * (if h = i then 1 else 0)) *
        ∑ h, a h k * f i h := by
      apply sum_congr rfl
      intro i _
      exact weight_product_marginal a ha j k hjk (fun h => if h = i then 1 else 0) (f i)
    _ = ∑ i, ∑ h, a i j * a h k * f i h := by
      simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
      simp_rw [mul_sum, mul_assoc]

theorem positive_weight_coordinate (a : Fin m → Fin n → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (σ : Fin n → Fin m) (hσ : 0 < weight a σ)
    (j : Fin n) : 0 < a (σ j) j := by
  have hz : a (σ j) j ≠ 0 := by
    intro h
    have : weight a σ = 0 := Finset.prod_eq_zero (mem_univ j) h
    linarith
  exact lt_of_le_of_ne (ha (σ j) j) (Ne.symm hz)

theorem exists_positive_weight_le (a : Fin m → Fin n → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (hs : ∀ j, ∑ i, a i j = 1)
    (F : (Fin n → Fin m) → ℝ) (B : ℝ)
    (hF : (∑ σ : Fin n → Fin m, weight a σ * F σ) ≤ B) :
    ∃ σ : Fin n → Fin m, 0 < weight a σ ∧ F σ ≤ B := by
  classical
  by_contra h
  push Not at h
  have hn := fun σ => weight_nonneg a ha σ
  have hmass := weight_sum a hs
  obtain ⟨σ, hσmem, hσ⟩ := (Finset.sum_pos_iff_of_nonneg (fun σ _ => hn σ)).mp
    (show 0 < ∑ σ : Fin n → Fin m, weight a σ by rw [hmass]; norm_num)
  have hstrict : (∑ σ : Fin n → Fin m, weight a σ * B) <
      ∑ σ : Fin n → Fin m, weight a σ * F σ := by
    apply Finset.sum_lt_sum
    · intro τ _
      obtain ht | ht := (hn τ).eq_or_lt
      · simp [← ht]
      · exact mul_le_mul_of_nonneg_left (h τ ht).le ht.le
    · exact ⟨σ, hσmem, mul_lt_mul_of_pos_left (h σ hσ) hσ⟩
  rw [← sum_mul, hmass, one_mul] at hstrict
  exact (not_lt_of_ge hF) hstrict

end PreemptionProof

noncomputable section
open Finset SkutellaCQP.Preempt
namespace PreemptionProof
variable {m n : ℕ}

theorem cprec_irrefl (P : PSched m n) (j : Fin n) : ¬ cprec P j j := by
  simp [cprec]

theorem cprec_trans (P : PSched m n) (j k l : Fin n)
    (hjk : cprec P j k) (hkl : cprec P k l) : cprec P j l := by
  rcases hjk with hjk | ⟨hjk, hij⟩ <;> rcases hkl with hkl | ⟨hkl, hkl'⟩
  · exact Or.inl (lt_trans hjk hkl)
  · exact Or.inl (hjk.trans_eq hkl)
  · exact Or.inl (hjk.trans_lt hkl)
  · exact Or.inr ⟨hjk.trans hkl, lt_trans hij hkl'⟩

theorem cprec_total (P : PSched m n) (j k : Fin n) (hjk : j ≠ k) :
    cprec P j k ∨ cprec P k j := by
  rcases lt_trichotomy (pcompl P j) (pcompl P k) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_or_gt_of_ne hjk with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

theorem cprec_completion_le (P : PSched m n) (j k : Fin n)
    (hjk : cprec P j k) : pcompl P j ≤ pcompl P k := by
  exact hjk.elim le_of_lt (fun h => h.1.le)

theorem earlierLoad_nonneg (p : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (σ : Fin n → Fin m) (j : Fin n) :
    0 ≤ earlierLoad p P σ j := by
  exact sum_nonneg fun k _ => (hp (σ j) k).le

theorem earlierLoad_precedence (p : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (σ : Fin n → Fin m) (k j : Fin n)
    (hkj : cprec P k j) (hσ : σ k = σ j) :
    earlierLoad p P σ k + p (σ k) k ≤ earlierLoad p P σ j := by
  classical
  let sk := univ.filter (fun l => cprec P l k ∧ σ l = σ k)
  let sj := univ.filter (fun l => cprec P l j ∧ σ l = σ j)
  have hk : k ∉ sk := by simp [sk, cprec_irrefl]
  have hsub : insert k sk ⊆ sj := by
    intro l hl
    rcases mem_insert.mp hl with rfl | hl
    · exact mem_filter.mpr ⟨mem_univ _, hkj, hσ⟩
    · rcases mem_filter.mp hl with ⟨_, hlk, hls⟩
      exact mem_filter.mpr ⟨mem_univ _, cprec_trans P l k j hlk hkj, hls.trans hσ⟩
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun l _ _ => (hp (σ j) l).le)
  rw [sum_insert hk] at hs
  simpa only [earlierLoad, sk, sj, hσ, add_comm] using hs

end PreemptionProof

noncomputable section
open Finset SkutellaCQP.Preempt
namespace PreemptionProof
variable {m n : ℕ}

def roundPiece (p : Fin m → Fin n → ℝ) (P : PSched m n)
    (κ : ℝ) (σ : Fin n → Fin m) (j : Fin n) : Piece m n :=
  {job := j, mach := σ j, start := κ * pcompl P j + earlierLoad p P σ j, stop := κ * pcompl P j + earlierLoad p P σ j + p (σ j) j}

theorem rounded_filter (p : Fin m → Fin n → ℝ) (P : PSched m n)
    (κ : ℝ) (σ : Fin n → Fin m) (j : Fin n) :
    (rounded p P κ σ).filter (fun q => q.job = j) = [roundPiece p P κ σ j] := by
  classical
  change (List.ofFn (roundPiece p P κ σ)).filter _ = _
  rw [List.ofFn_eq_map, List.filter_map]
  change List.map (roundPiece p P κ σ)
    ((List.finRange n).filter (fun k => k = j)) = _
  rw [List.filter_eq]
  simp

theorem rounded_nonpreemptive (p : Fin m → Fin n → ℝ) (P : PSched m n)
    (κ : ℝ) (σ : Fin n → Fin m) : Nonpreemptive (rounded p P κ σ) := by
  intro j
  rw [rounded_filter]
  rfl

theorem rounded_completion (p : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (κ : ℝ) (hκ : 0 ≤ κ)
    (σ : Fin n → Fin m) (j : Fin n) :
    pcompl (rounded p P κ σ) j =
      κ * pcompl P j + earlierLoad p P σ j + p (σ j) j := by
  have hs : 0 ≤ κ * pcompl P j + earlierLoad p P σ j + p (σ j) j :=
    add_nonneg (add_nonneg (mul_nonneg hκ (completion_nonneg P j))
      (earlierLoad_nonneg p P hp σ j)) (hp (σ j) j).le
  unfold pcompl
  rw [rounded_filter]
  simpa only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, roundPiece, pcompl]
    using max_eq_left hs

theorem rounded_piece_precedence (p : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (κ : ℝ) (hκ : 0 ≤ κ)
    (σ : Fin n → Fin m) (k j : Fin n) (hkj : cprec P k j) (hσ : σ k = σ j) :
    (roundPiece p P κ σ k).stop ≤ (roundPiece p P κ σ j).start := by
  have hload := earlierLoad_precedence p P hp σ k j hkj hσ
  have hc := mul_le_mul_of_nonneg_left (cprec_completion_le P k j hkj) hκ
  change κ * pcompl P k + earlierLoad p P σ k + p (σ k) k ≤
    κ * pcompl P j + earlierLoad p P σ j
  linarith

theorem rounded_feasible (p r : Fin m → Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (κ : ℝ) (hκ : 0 ≤ κ)
    (σ : Fin n → Fin m)
    (hrσ : ∀ j, r (σ j) j ≤ κ * pcompl P j) :
    PFeasible p r (rounded p P κ σ) := by
  classical
  have hlen : (rounded p P κ σ).length = n := by simp [rounded]
  have hget (a : Fin (rounded p P κ σ).length) :
      (rounded p P κ σ).get a = roundPiece p P κ σ (Fin.cast hlen a) := by
    change (List.ofFn (roundPiece p P κ σ)).get a = _
    exact List.get_ofFn (roundPiece p P κ σ) a
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    change q ∈ List.ofFn (roundPiece p P κ σ) at hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    change r (σ j) j ≤ κ * pcompl P j + earlierLoad p P σ j ∧
      κ * pcompl P j + earlierLoad p P σ j ≤
        κ * pcompl P j + earlierLoad p P σ j + p (σ j) j
    constructor
    · exact (hrσ j).trans (le_add_of_nonneg_right (earlierLoad_nonneg p P hp σ j))
    · exact le_add_of_nonneg_right (hp (σ j) j).le
  · intro a b hab hmach
    rw [hget a, hget b] at hmach ⊢
    change σ (Fin.cast hlen a) = σ (Fin.cast hlen b) at hmach
    have hj : Fin.cast hlen a ≠ Fin.cast hlen b := by
      intro h
      exact hab (Fin.ext (congrArg (fun x : Fin n => x.val) h))
    rcases cprec_total P _ _ hj with h | h
    · exact Or.inl (rounded_piece_precedence p P hp κ hκ σ _ _ h hmach)
    · exact Or.inr (rounded_piece_precedence p P hp κ hκ σ _ _ h hmach.symm)
  · intro a b hab hj
    rw [hget a, hget b] at hj
    change Fin.cast hlen a = Fin.cast hlen b at hj
    exact False.elim (hab (Fin.ext (congrArg (fun x : Fin n => x.val) hj)))
  · intro j
    rw [rounded_filter]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, roundPiece]
    have h : (κ * pcompl P j + earlierLoad p P σ j + p (σ j) j -
        (κ * pcompl P j + earlierLoad p P σ j)) = p (σ j) j := by ring
    rw [h, div_self (hp (σ j) j).ne']

end PreemptionProof

noncomputable section
open Finset SkutellaCQP.Preempt
namespace PreemptionProof
variable {m n : ℕ}

theorem expected_earlierLoad (a p : Fin m → Fin n → ℝ) (P : PSched m n)
    (ha : ∀ j, ∑ i, a i j = 1) (j : Fin n) :
    (∑ σ : Fin n → Fin m, weight a σ * earlierLoad p P σ j) =
      ∑ i, a i j * ∑ k ∈ univ.filter (fun k => cprec P k j), a i k * p i k := by
  classical
  let s := univ.filter (fun k => cprec P k j)
  have hs (σ : Fin n → Fin m) : earlierLoad p P σ j =
      ∑ k ∈ s, if σ k = σ j then p (σ j) k else 0 := by
    simp only [earlierLoad, s, sum_filter]
    apply sum_congr rfl
    intro k _
    by_cases hc : cprec P k j <;> by_cases he : σ k = σ j <;> simp [hc, he]
  calc
    _ = ∑ k ∈ s, ∑ σ : Fin n → Fin m,
        weight a σ * (if σ k = σ j then p (σ j) k else 0) := by
      simp_rw [hs, mul_sum]
      rw [sum_comm]
    _ = ∑ k ∈ s, ∑ i, a i j * a i k * p i k := by
      apply sum_congr rfl
      intro k hk
      have hjk : j ≠ k := by
        intro h
        subst k
        exact cprec_irrefl P j (mem_filter.mp hk).2
      have h := weight_pair a ha j k hjk (fun i h => if h = i then p i k else 0)
      simpa [mul_ite] using h
    _ = ∑ i, a i j * ∑ k ∈ s, a i k * p i k := by
      rw [sum_comm]
      simp_rw [mul_sum, mul_assoc]

theorem expected_rounded_completion (p r : Fin m → Fin n → ℝ)
    (P : PSched m n) (hp : ∀ i j, 0 < p i j)
    (hr : ∀ i j, 0 ≤ r i j) (hP : PFeasible p r P)
    (κ : ℝ) (hκ : 0 ≤ κ) (j : Fin n) :
    (∑ σ : Fin n → Fin m, weight (fraction p P) σ * pcompl (rounded p P κ σ) j)
      ≤ (κ + 2) * pcompl P j := by
  classical
  let a := fraction p P
  have ha : ∀ i j, 0 ≤ a i j := fraction_nonneg p r P hp hr hP
  have has : ∀ j, ∑ i, a i j = 1 := fraction_sum_one p r P hp hr hP
  have hown := job_time_bound p r P hp hr hP j
  have hload : (∑ σ : Fin n → Fin m, weight a σ * earlierLoad p P σ j) ≤ pcompl P j := by
    rw [expected_earlierLoad a p P has j]
    calc
      _ ≤ ∑ i, a i j * pcompl P j := by
        apply sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (machine_prefix_bound p r P hp hr hP i j) (ha i j)
      _ = pcompl P j := by rw [← sum_mul, has j, one_mul]
  have hmargin := weight_marginal a has j (fun i => p i j)
  have hmass := weight_sum a has
  have heq : (∑ σ : Fin n → Fin m, weight a σ * pcompl (rounded p P κ σ) j) =
      κ * pcompl P j + (∑ σ : Fin n → Fin m, weight a σ * earlierLoad p P σ j) +
        ∑ i, a i j * p i j := by
    simp_rw [rounded_completion p P hp κ hκ, mul_add, sum_add_distrib]
    rw [← sum_mul, hmass, one_mul, hmargin]
  change (∑ σ : Fin n → Fin m, weight a σ * pcompl (rounded p P κ σ) j) ≤ _
  rw [heq]
  change (∑ i, a i j * p i j) ≤ pcompl P j at hown
  nlinarith only [hown, hload]

theorem expected_rounded_value (p r : Fin m → Fin n → ℝ)
    (w : Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (hr : ∀ i j, 0 ≤ r i j) (hP : PFeasible p r P)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    (∑ σ : Fin n → Fin m, weight (fraction p P) σ * pval w (rounded p P κ σ))
      ≤ (κ + 2) * pval w P := by
  classical
  calc
    _ = ∑ j, w j * ∑ σ : Fin n → Fin m,
        weight (fraction p P) σ * pcompl (rounded p P κ σ) j := by
      simp only [pval, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro σ _
      ring
    _ ≤ ∑ j, w j * ((κ + 2) * pcompl P j) := by
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (expected_rounded_completion p r P hp hr hP κ hκ j) (hw j)
    _ = (κ + 2) * pval w P := by
      simp only [pval, mul_sum]
      apply sum_congr rfl
      intro j _
      ring

theorem rounding_exists (p r : Fin m → Fin n → ℝ)
    (w : Fin n → ℝ) (P : PSched m n)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (hr : ∀ i j, 0 ≤ r i j) (hP : PFeasible p r P)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hrelease : ∀ i j, 0 < fraction p P i j → r i j ≤ κ * pcompl P j) :
    ∃ S : PSched m n, PFeasible p r S ∧ Nonpreemptive S ∧
      pval w S ≤ (κ + 2) * pval w P := by
  have ha := fraction_nonneg p r P hp hr hP
  have has := fraction_sum_one p r P hp hr hP
  obtain ⟨σ, hσ, hval⟩ := exists_positive_weight_le (fraction p P) ha has
    (fun σ => pval w (rounded p P κ σ)) ((κ + 2) * pval w P)
    (expected_rounded_value p r w P hp hw hr hP κ hκ)
  refine ⟨rounded p P κ σ, rounded_feasible p r P hp κ hκ σ ?_,
    rounded_nonpreemptive p P κ σ, hval⟩
  intro j
  exact hrelease (σ j) j (positive_weight_coordinate (fraction p P) ha σ hσ j)

end PreemptionProof

namespace SkutellaCQP.Preempt

theorem power_of_preemption {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j) :
    ∀ P : PSched m n, PFeasible p r P →
      (∃ S : PSched m n, PFeasible p r S ∧ Nonpreemptive S ∧ pval w S ≤ 3 * pval w P) ∧
      ((∀ i j, r i j = 0) →
        ∃ S : PSched m n, PFeasible p r S ∧ Nonpreemptive S ∧ pval w S ≤ 2 * pval w P) := by
  intro P hP
  constructor
  · obtain ⟨S, hS, hN, hval⟩ := PreemptionProof.rounding_exists p r w P hp hw hr hP 1
      (by norm_num) (by
        intro i j ha
        simpa only [one_mul] using PreemptionProof.fraction_release p r P hp hr hP i j ha)
    exact ⟨S, hS, hN, by norm_num at hval ⊢; exact hval⟩
  · intro hz
    obtain ⟨S, hS, hN, hval⟩ := PreemptionProof.rounding_exists p r w P hp hw hr hP 0
      (by norm_num) (by intro i j _; simp only [hz, zero_mul, le_refl])
    exact ⟨S, hS, hN, by simpa only [zero_add] using hval⟩

end SkutellaCQP.Preempt

open SkutellaCQP.Preempt


theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j) :
    ∀ P : PSched m n, PFeasible p r P →
      (∃ S : PSched m n, PFeasible p r S ∧ Nonpreemptive S ∧ pval w S ≤ 3 * pval w P) ∧
      ((∀ i j, r i j = 0) →
        ∃ S : PSched m n, PFeasible p r S ∧ Nonpreemptive S ∧ pval w S ≤ 2 * pval w P) := by
  exact SkutellaCQP.Preempt.power_of_preemption p w r hp hw hr
