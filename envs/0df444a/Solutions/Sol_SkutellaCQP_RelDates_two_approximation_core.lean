-- Prove2me | solution 1 for SkutellaCQP.RelDates.two_approximation_core
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T00:25:02.499007+00:00
-- url     : https://prove2.me/submissions/36f202b3-cdb3-4f4f-b2fe-647867deb013

import Mathlib
import Definitions.Def_SkutellaCQP_RelDates_Setting

set_option autoImplicit false

namespace SkutAuxdd60

open Finset SkutellaCQP.RelDates

theorem prec_irrefl {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (i : Fin m) (a : Fin n) : ¬ SkutellaCQP.NoRel.prec p w i a a := by
  unfold SkutellaCQP.NoRel.prec
  rintro (h | ⟨_, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

theorem prec_asymm {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (i : Fin m) (a b : Fin n) (h1 : SkutellaCQP.NoRel.prec p w i a b) :
    ¬ SkutellaCQP.NoRel.prec p w i b a := by
  unfold SkutellaCQP.NoRel.prec at *
  rintro h2
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · linarith
  · linarith
  · linarith
  · exact lt_asymm h1' h2'

theorem prec_le {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (i : Fin m) (a b : Fin n) (h : SkutellaCQP.NoRel.prec p w i a b) :
    w b * p i a ≤ w a * p i b := by
  unfold SkutellaCQP.NoRel.prec at h
  rcases h with h | ⟨h, _⟩
  · linarith
  · linarith

theorem prec_total {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (i : Fin m) (a b : Fin n) (hab : a ≠ b) :
    SkutellaCQP.NoRel.prec p w i a b ∨ SkutellaCQP.NoRel.prec p w i b a := by
  unfold SkutellaCQP.NoRel.prec
  rcases lt_trichotomy (w a * p i b) (w b * p i a) with h | h | h
  · right; left; linarith
  · rcases lt_or_gt_of_ne hab with h' | h'
    · left; right; exact ⟨h, h'⟩
    · right; right; exact ⟨h.symm, h'⟩
  · left; left; linarith

theorem prec_trans {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (i : Fin m) (hp : ∀ j, 0 < p i j) {a b c : Fin n}
    (h1 : SkutellaCQP.NoRel.prec p w i a b) (h2 : SkutellaCQP.NoRel.prec p w i b c) : SkutellaCQP.NoRel.prec p w i a c := by
  unfold SkutellaCQP.NoRel.prec at *
  have key : p i b * (w a * p i c - w c * p i a) =
      p i c * (w a * p i b - w b * p i a) + p i a * (w b * p i c - w c * p i b) := by ring
  have hpa := hp a
  have hpb := hp b
  have hpc := hp c
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left
    have e1 : 0 < p i c * (w a * p i b - w b * p i a) := mul_pos hpc (by linarith)
    have e2 : 0 < p i a * (w b * p i c - w c * p i b) := mul_pos hpa (by linarith)
    by_contra hc
    push Not at hc
    have : p i b * (w a * p i c - w c * p i a) ≤ p i b * 0 :=
      mul_le_mul_of_nonneg_left (by linarith) hpb.le
    linarith
  · left
    have e1 : 0 < p i c * (w a * p i b - w b * p i a) := mul_pos hpc (by linarith)
    have e2 : p i a * (w b * p i c - w c * p i b) = 0 := by rw [h2]; ring
    by_contra hc
    push Not at hc
    have : p i b * (w a * p i c - w c * p i a) ≤ p i b * 0 :=
      mul_le_mul_of_nonneg_left (by linarith) hpb.le
    linarith
  · left
    have e1 : p i c * (w a * p i b - w b * p i a) = 0 := by rw [h1]; ring
    have e2 : 0 < p i a * (w b * p i c - w c * p i b) := mul_pos hpa (by linarith)
    by_contra hc
    push Not at hc
    have : p i b * (w a * p i c - w c * p i a) ≤ p i b * 0 :=
      mul_le_mul_of_nonneg_left (by linarith) hpb.le
    linarith
  · right
    refine ⟨?_, lt_trans h1' h2'⟩
    have e1 : p i c * (w a * p i b - w b * p i a) = 0 := by rw [h1]; ring
    have e2 : p i a * (w b * p i c - w c * p i b) = 0 := by rw [h2]; ring
    have h0 : p i b * (w a * p i c - w c * p i a) = 0 := by rw [key, e1, e2]; ring
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hpb.ne'
    · linarith

theorem sym_le {n : ℕ} (h g : Fin n → Fin n → ℝ) (H : ∀ j k, h j k + h k j ≤ g j k + g k j) :
    ∑ j, ∑ k, h j k ≤ ∑ j, ∑ k, g j k := by
  have e1 : ∑ j, ∑ k, h k j = ∑ j, ∑ k, h j k := Finset.sum_comm
  have e2 : ∑ j, ∑ k, g k j = ∑ j, ∑ k, g j k := Finset.sum_comm
  have : ∑ j, ∑ k, (h j k + h k j) ≤ ∑ j, ∑ k, (g j k + g k j) :=
    Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => H j k))
  simp only [Finset.sum_add_distrib] at this
  linarith

theorem rho_mono {m n : ℕ} (r : Fin m → Fin n → ℝ) (i : Fin m) : Monotone (rho r i) :=
  Tuple.monotone_sort (r i)

theorem rho_exists {m n : ℕ} (r : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    rho r i ((Tuple.sort (r i)).symm j) = r i j := by
  unfold rho; rw [Equiv.apply_symm_apply]

theorem sStartN_zero {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) (i : Fin m) (h : 0 < n) :
    sStartN p r a i 0 = rho r i ⟨0, h⟩ := by
  simp only [sStartN, dif_pos h]

theorem sStartN_succ {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) (i : Fin m) (k : ℕ) (h : k + 1 < n) :
    sStartN p r a i (k + 1) = max (rho r i ⟨k + 1, h⟩)
        (sStartN p r a i k + ∑ j, a i ⟨k, by omega⟩ j * p i j) := by
  simp only [sStartN, dif_pos h]

theorem rho_le_sStart {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) (i : Fin m) (k : Fin n) :
    rho r i k ≤ sStart p r a i k := by
  unfold sStart
  obtain ⟨kv, hk⟩ := k
  cases kv with
  | zero => rw [sStartN_zero p r a i hk]
  | succ k' => rw [sStartN_succ p r a i k' hk]; exact le_max_left _ _

theorem sStartN_step {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) (i : Fin m) (k : ℕ) (h : k + 1 < n) :
    sStartN p r a i k + ∑ j, a i ⟨k, by omega⟩ j * p i j ≤ sStartN p r a i (k + 1) := by
  rw [sStartN_succ p r a i k h]; exact le_max_right _ _

theorem sStartN_mono {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) (i : Fin m)
    (hL : ∀ t : Fin n, 0 ≤ ∑ j, a i t j * p i j) (k : ℕ) :
    ∀ k', k ≤ k' → k' < n → sStartN p r a i k ≤ sStartN p r a i k' := by
  intro k' hkk'
  induction k', hkk' using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ k'' hk'' ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := sStartN_step p r a i k'' h
    have h3 := hL ⟨k'', by omega⟩
    linarith

theorem slotInd_nonneg {m n : ℕ} (τ : Fin n → Fin m × Fin n) (i : Fin m) (k j : Fin n) :
    0 ≤ slotInd τ i k j := by
  unfold slotInd; split_ifs <;> norm_num

theorem load_eq {m n : ℕ} (p : Fin m → Fin n → ℝ) (τ : Fin n → Fin m × Fin n) (i : Fin m)
    (k : Fin n) :
    ∑ j, slotInd τ i k j * p i j = ∑ j ∈ univ.filter (fun j => τ j = (i, k)), p i j := by
  rw [sum_filter]; refine sum_congr rfl (fun j _ => ?_)
  unfold slotInd; split_ifs <;> simp

theorem load_nonneg {m n : ℕ} (p : Fin m → Fin n → ℝ) (hp : ∀ i j, 0 < p i j)
    (τ : Fin n → Fin m × Fin n) (i : Fin m) (k : Fin n) :
    0 ≤ ∑ j, slotInd τ i k j * p i j :=
  sum_nonneg (fun j _ => mul_nonneg (slotInd_nonneg τ i k j) (hp i j).le)

theorem start_eq {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (τ : Fin n → Fin m × Fin n) (j : Fin n) :
    (schedOf p w r τ).start j = sStart p r (slotInd τ) (τ j).1 (τ j).2 +
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w (τ j).1 j' j ∧ τ j' = τ j),
        p (τ j).1 j' := by
  simp only [schedOf, Cslot]; ring

theorem compl_eq {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (τ : Fin n → Fin m × Fin n) (j : Fin n) :
    SkutellaCQP.RelDates.compl p (schedOf p w r τ) j = Cslot p w r τ j := by
  simp only [SkutellaCQP.RelDates.compl, schedOf]; ring

/-- `j` finishes before `j'` starts when `j'` is in a later slot of the same machine, or in the
same slot and later in Smith's order. -/
theorem before {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (τ : Fin n → Fin m × Fin n) (j j' : Fin n)
    (hm : (τ j).1 = (τ j').1)
    (hord : (τ j).2 < (τ j').2 ∨ (τ j = τ j' ∧ SkutellaCQP.NoRel.prec p w (τ j).1 j j')) :
    SkutellaCQP.RelDates.compl p (schedOf p w r τ) j ≤ (schedOf p w r τ).start j' := by
  rw [compl_eq, start_eq]
  set i := (τ j).1 with hi
  set F := univ.filter (fun j'' => SkutellaCQP.NoRel.prec p w i j'' j ∧ τ j'' = τ j) with hF
  have hjF : j ∉ F := by
    rw [hF, mem_filter]; exact fun h => prec_irrefl p w i j h.2.1
  have hnn : 0 ≤ ∑ j'' ∈ univ.filter (fun j'' => SkutellaCQP.NoRel.prec p w (τ j').1 j'' j' ∧
      τ j'' = τ j'), p (τ j').1 j'' := sum_nonneg (fun _ _ => (hp _ _).le)
  have hC : Cslot p w r τ j = sStart p r (slotInd τ) i (τ j).2 + ∑ j'' ∈ insert j F, p i j'' := by
    rw [sum_insert hjF]; simp only [Cslot]; rw [← hi, ← hF]; ring
  rw [hC]
  rcases hord with hlt | ⟨heq, hpr⟩
  · -- later slot
    have hsub : insert j F ⊆ univ.filter (fun j'' => τ j'' = (i, (τ j).2)) := by
      intro x hx
      rw [mem_insert] at hx
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rcases hx with rfl | hx
      · rfl
      · rw [hF, mem_filter] at hx; rw [hx.2.2]
    have h1 : ∑ j'' ∈ insert j F, p i j'' ≤
        ∑ j'' ∈ univ.filter (fun j'' => τ j'' = (i, (τ j).2)), p i j'' :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (hp _ _).le)
    rw [← load_eq] at h1
    have hk1 : (τ j).2.val + 1 < n := by have := (τ j').2.isLt; omega
    have h2 := sStartN_step p r (slotInd τ) i (τ j).2.val hk1
    have h3 := sStartN_mono p r (slotInd τ) i (fun t => load_nonneg p hp τ i t)
      ((τ j).2.val + 1) (τ j').2.val (by omega) (τ j').2.isLt
    have e : sStart p r (slotInd τ) (τ j').1 (τ j').2 = sStartN p r (slotInd τ) i (τ j').2.val := by
      rw [← hm]; rfl
    have e2 : sStart p r (slotInd τ) i (τ j).2 = sStartN p r (slotInd τ) i (τ j).2.val := rfl
    have e3 : (⟨(τ j).2.val, by omega⟩ : Fin n) = (τ j).2 := rfl
    rw [e3] at h2
    rw [e, e2]
    linarith
  · -- same slot, Smith order
    have hsub : insert j F ⊆ univ.filter (fun j'' => SkutellaCQP.NoRel.prec p w (τ j').1 j'' j' ∧
        τ j'' = τ j') := by
      intro x hx
      rw [mem_insert] at hx
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rcases hx with rfl | hx
      · exact ⟨hm ▸ hpr, heq⟩
      · rw [hF, mem_filter] at hx
        exact ⟨hm ▸ prec_trans p w i (hp i) hx.2.1 hpr, hx.2.2.trans heq⟩
    have h1 := sum_le_sum_of_subset_of_nonneg (f := fun j'' => p i j'') hsub
      (fun _ _ _ => (hp _ _).le)
    have e : sStart p r (slotInd τ) (τ j').1 (τ j').2 = sStart p r (slotInd τ) i (τ j).2 := by
      rw [← heq]
    rw [e]
    have e4 : (τ j').1 = i := hm.symm
    simp only [e4] at h1 ⊢
    linarith

theorem part1 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (τ : Fin n → Fin m × Fin n) (hτ : SlotFeasible r τ) :
    SFeasible p r (schedOf p w r τ) ∧
      ∀ j, SkutellaCQP.RelDates.compl p (schedOf p w r τ) j = Cslot p w r τ j := by
  refine ⟨⟨fun j => ?_, fun j j' hne hm => ?_⟩, fun j => compl_eq p w r τ j⟩
  · have h1 := hτ j
    have h2 := rho_le_sStart p r (slotInd τ) (τ j).1 (τ j).2
    have h3 : 0 ≤ ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w (τ j).1 j' j ∧
        τ j' = τ j), p (τ j).1 j' := sum_nonneg (fun _ _ => (hp _ _).le)
    rw [start_eq]
    show r (τ j).1 j ≤ _
    linarith
  · change (τ j).1 = (τ j').1 at hm
    rcases lt_trichotomy (τ j).2 (τ j').2 with h | h | h
    · left; exact before p w r hp τ j j' hm (Or.inl h)
    · have heq : τ j = τ j' := Prod.ext hm h
      rcases prec_total p w (τ j).1 j j' hne with hpr | hpr
      · left; exact before p w r hp τ j j' hm (Or.inr ⟨heq, hpr⟩)
      · right; exact before p w r hp τ j' j hm.symm (Or.inr ⟨heq.symm, heq ▸ hpr⟩)
    · right; exact before p w r hp τ j' j hm.symm (Or.inl h)

noncomputable def LN {m n : ℕ} (p : Fin m → Fin n → ℝ) (a : Fin m → Fin n → Fin n → ℝ)
    (i : Fin m) (t : ℕ) : ℝ :=
  if h : t < n then ∑ j, a i ⟨t, h⟩ j * p i j else 0

theorem sStartN_le {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (a : Fin m → Fin n → Fin n → ℝ) (i : Fin m) (hL : ∀ t : Fin n, 0 ≤ ∑ j, a i t j * p i j) :
    ∀ k (hk : k < n), sStartN p r a i k ≤ rho r i ⟨k, hk⟩ + ∑ t ∈ range k, LN p a i t := by
  have hLN : ∀ t, 0 ≤ LN p a i t := fun t => by
    unfold LN; split_ifs with h
    · exact hL _
    · exact le_refl _
  intro k
  induction k with
  | zero => intro hk; rw [sStartN_zero p r a i hk]; simp
  | succ k ih =>
    intro hk
    rw [sStartN_succ p r a i k hk, sum_range_succ]
    have h1 := ih (by omega)
    have h2 : rho r i ⟨k, by omega⟩ ≤ rho r i ⟨k + 1, hk⟩ :=
      rho_mono r i (Fin.mk_le_mk.2 (by omega))
    have h3 : LN p a i k = ∑ j, a i ⟨k, by omega⟩ j * p i j := by
      unfold LN; rw [dif_pos (by omega)]
    have h4 : 0 ≤ ∑ t ∈ range k, LN p a i t := sum_nonneg (fun t _ => hLN t)
    apply max_le <;> linarith [hLN k]

def Ind {m n : ℕ} (τ : Fin n → Fin m × Fin n) (j : Fin n) (x : Fin m × Fin n) : ℝ :=
  if τ j = x then 1 else 0

theorem sum_ind {m n : ℕ} (τ : Fin n → Fin m × Fin n) (j : Fin n) (F : Fin m → Fin n → ℝ) :
    ∑ i, ∑ k, Ind τ j (i, k) * F i k = F (τ j).1 (τ j).2 := by
  rw [← Fintype.sum_prod_type' (f := fun i k => Ind τ j (i, k) * F i k)]
  simp [Ind]

noncomputable def G {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (j : Fin n) (τ : Fin n → Fin m × Fin n) (i : Fin m) (k : Fin n) : ℝ :=
  rho r i k + p i j +
    ∑ t ∈ range k.val, (if h : t < n then ∑ j' ∈ univ.erase j, Ind τ j' (i, ⟨t, h⟩) * p i j' else 0) +
    ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), Ind τ j' (i, k) * p i j'

theorem Cslot_le_G {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (τ : Fin n → Fin m × Fin n) (j : Fin n) :
    Cslot p w r τ j ≤ G p w r j τ (τ j).1 (τ j).2 := by
  rcases hx : τ j with ⟨i, k⟩
  have e1 : Cslot p w r τ j = sStartN p r (slotInd τ) i k.val + p i j +
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), Ind τ j' (i, k) * p i j' := by
    simp only [Cslot, hx, sStart]
    rw [← filter_filter, sum_filter]
    congr 1
    refine sum_congr rfl (fun j' _ => ?_)
    unfold Ind; split_ifs <;> simp
  have e2 : ∀ t ∈ range k.val, LN p (slotInd τ) i t =
      (if h : t < n then ∑ j' ∈ univ.erase j, Ind τ j' (i, ⟨t, h⟩) * p i j' else 0) := by
    intro t ht
    rw [mem_range] at ht
    unfold LN
    split_ifs with h
    · rw [← add_sum_erase _ _ (mem_univ j)]
      have h0 : slotInd τ i ⟨t, h⟩ j = 0 := by
        unfold slotInd; rw [if_neg]; rw [hx]; intro hc
        have := congrArg (fun z => z.2.val) hc; simp at this; omega
      rw [h0, zero_mul, zero_add]; rfl
    · rfl
  have h3 := sStartN_le p r (slotInd τ) i (fun t => load_nonneg p hp τ i t) k.val k.isLt
  rw [sum_congr rfl e2] at h3
  rw [e1]; unfold G
  linarith

theorem E1 {m n : ℕ} (a : Fin m → Fin n → Fin n → ℝ) (μ : (Fin n → Fin m × Fin n) → ℝ)
    (hμ : IsPairwiseRounding a μ) (j : Fin n) (x : Fin m × Fin n) (c : ℝ) :
    ∑ τ, μ τ * (Ind τ j x * c) = a x.1 x.2 j * c := by
  have h := hμ.2.2.1 j x.1 x.2
  rw [sum_filter] at h
  simp only [Prod.mk.eta] at h
  rw [← h, sum_mul]
  refine sum_congr rfl (fun τ _ => ?_)
  unfold Ind; split_ifs <;> simp

theorem E2 {m n : ℕ} (a : Fin m → Fin n → Fin n → ℝ) (μ : (Fin n → Fin m × Fin n) → ℝ)
    (hμ : IsPairwiseRounding a μ) (j j' : Fin n) (hne : j ≠ j') (x y : Fin m × Fin n) (c : ℝ) :
    ∑ τ, μ τ * (Ind τ j x * Ind τ j' y * c) = a x.1 x.2 j * a y.1 y.2 j' * c := by
  have h := hμ.2.2.2 j j' hne x y
  rw [sum_filter] at h
  rw [← h, sum_mul]
  refine sum_congr rfl (fun τ _ => ?_)
  unfold Ind
  by_cases h1 : τ j = x <;> by_cases h2 : τ j' = y <;> simp [h1, h2]

theorem slot_bound {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hr : ∀ i j, 0 ≤ r i j)
    (a : Fin m → Fin n → Fin n → ℝ) (ha : CQPFeasible p r a)
    (μ : (Fin n → Fin m × Fin n) → ℝ) (hμ : IsPairwiseRounding a μ) (j : Fin n) (i : Fin m)
    (k : Fin n) :
    ∑ τ, μ τ * (Ind τ j (i, k) * G p w r j τ i k) ≤
      a i k j * (2 * rho r i k + p i j +
        ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), a i k j' * p i j') := by
  have ha0 : ∀ i k j, 0 ≤ a i k j := ha.1.2.2
  set PF := univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j) with hPF
  have expand : ∀ τ, Ind τ j (i, k) * G p w r j τ i k =
      Ind τ j (i, k) * (rho r i k + p i j) +
      ∑ t ∈ range k.val, (if h : t < n then
        ∑ j' ∈ univ.erase j, Ind τ j (i, k) * Ind τ j' (i, ⟨t, h⟩) * p i j' else 0) +
      ∑ j' ∈ PF, Ind τ j (i, k) * Ind τ j' (i, k) * p i j' := by
    intro τ
    unfold G
    have hA : Ind τ j (i, k) * ∑ t ∈ range k.val, (if h : t < n then
        ∑ j' ∈ univ.erase j, Ind τ j' (i, ⟨t, h⟩) * p i j' else 0) =
        ∑ t ∈ range k.val, (if h : t < n then
        ∑ j' ∈ univ.erase j, Ind τ j (i, k) * Ind τ j' (i, ⟨t, h⟩) * p i j' else 0) := by
      rw [mul_sum]; refine sum_congr rfl (fun t _ => ?_)
      split_ifs
      · rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
      · simp
    have hB : Ind τ j (i, k) * ∑ j' ∈ PF, Ind τ j' (i, k) * p i j' =
        ∑ j' ∈ PF, Ind τ j (i, k) * Ind τ j' (i, k) * p i j' := by
      rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
    rw [← hA, ← hB]; ring
  have hsplit : ∑ τ, μ τ * (Ind τ j (i, k) * G p w r j τ i k) =
      ∑ τ, μ τ * (Ind τ j (i, k) * (rho r i k + p i j)) +
      ∑ τ, μ τ * ∑ t ∈ range k.val, (if h : t < n then
        ∑ j' ∈ univ.erase j, Ind τ j (i, k) * Ind τ j' (i, ⟨t, h⟩) * p i j' else 0) +
      ∑ τ, μ τ * ∑ j' ∈ PF, Ind τ j (i, k) * Ind τ j' (i, k) * p i j' := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun τ _ => ?_)
    rw [expand τ]; ring
  rw [hsplit]
  have eA : ∑ τ, μ τ * (Ind τ j (i, k) * (rho r i k + p i j)) = a i k j * (rho r i k + p i j) :=
    E1 a μ hμ j (i, k) _
  have eC : ∑ τ, μ τ * ∑ j' ∈ PF, Ind τ j (i, k) * Ind τ j' (i, k) * p i j' =
      ∑ j' ∈ PF, a i k j * a i k j' * p i j' := by
    simp_rw [mul_sum]; rw [sum_comm]
    refine sum_congr rfl (fun j' hj' => ?_)
    have hne : j ≠ j' := by
      intro h; rw [hPF, mem_filter] at hj'; rw [h] at hj'; exact prec_irrefl p w i j' hj'.2
    exact E2 a μ hμ j j' hne (i, k) (i, k) _
  -- the middle (earlier slots) term
  set Rn : ℕ → ℝ := fun t => if h : t < n then rho r i ⟨t, h⟩ else 0 with hRn
  have eB : ∑ τ, μ τ * ∑ t ∈ range k.val, (if h : t < n then
        ∑ j' ∈ univ.erase j, Ind τ j (i, k) * Ind τ j' (i, ⟨t, h⟩) * p i j' else 0) ≤
      ∑ t ∈ range k.val, a i k j * (Rn (t + 1) - Rn t) := by
    simp_rw [mul_sum]; rw [sum_comm]
    refine sum_le_sum (fun t ht => ?_)
    rw [mem_range] at ht
    have htn : t < n := by have := k.isLt; omega
    have ht1 : t + 1 < n := by have := k.isLt; omega
    have e : ∀ τ, μ τ * (if h : t < n then
        ∑ j' ∈ univ.erase j, Ind τ j (i, k) * Ind τ j' (i, ⟨t, h⟩) * p i j' else 0) =
        ∑ j' ∈ univ.erase j, μ τ * (Ind τ j (i, k) * Ind τ j' (i, ⟨t, htn⟩) * p i j') := by
      intro τ; rw [dif_pos htn, mul_sum]
    simp_rw [e]; rw [sum_comm]
    have e2 : ∀ j' ∈ univ.erase j, ∑ τ, μ τ * (Ind τ j (i, k) * Ind τ j' (i, ⟨t, htn⟩) * p i j') =
        a i k j * (a i ⟨t, htn⟩ j' * p i j') := by
      intro j' hj'
      rw [E2 a μ hμ j j' (Ne.symm (ne_of_mem_erase hj')) (i, k) (i, ⟨t, htn⟩)]; ring
    rw [sum_congr rfl e2, ← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (ha0 i k j)
    have hsub : ∑ j' ∈ univ.erase j, a i ⟨t, htn⟩ j' * p i j' ≤ ∑ j', a i ⟨t, htn⟩ j' * p i j' :=
      sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
        (fun _ _ _ => mul_nonneg (ha0 _ _ _) (hp _ _).le)
    have hcap := ha.2 i ⟨t, htn⟩ ht1
    have r1 : Rn (t + 1) = rho r i ⟨t + 1, ht1⟩ := by rw [hRn]; simp only [dif_pos ht1]
    have r0 : Rn t = rho r i ⟨t, htn⟩ := by rw [hRn]; simp only [dif_pos htn]
    rw [r1, r0]
    exact hsub.trans hcap
  rw [← mul_sum, sum_range_sub] at eB
  have rk : Rn k.val = rho r i k := by rw [hRn]; simp only [dif_pos k.isLt]
  have r0 : 0 ≤ Rn 0 := by
    rw [hRn]; simp only
    split_ifs
    · unfold rho; exact hr _ _
    · exact le_refl _
  rw [rk] at eB
  rw [eA, eC]
  have hSnn : 0 ≤ ∑ j' ∈ PF, a i k j' * p i j' :=
    sum_nonneg (fun _ _ => mul_nonneg (ha0 _ _ _) (hp _ _).le)
  have eC' : ∑ j' ∈ PF, a i k j * a i k j' * p i j' = a i k j * ∑ j' ∈ PF, a i k j' * p i j' := by
    rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
  rw [eC']
  have := ha0 i k j
  have := mul_nonneg (ha0 i k j) r0
  nlinarith

theorem E_Cslot_le {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hr : ∀ i j, 0 ≤ r i j)
    (a : Fin m → Fin n → Fin n → ℝ) (ha : CQPFeasible p r a)
    (μ : (Fin n → Fin m × Fin n) → ℝ) (hμ : IsPairwiseRounding a μ) (j : Fin n) :
    E μ (fun τ => Cslot p w r τ j) ≤ 2 * Cbar p w r a j := by
  have ha0 : ∀ i k j, 0 ≤ a i k j := ha.1.2.2
  have s1 : E μ (fun τ => Cslot p w r τ j) ≤
      ∑ τ, μ τ * ∑ i, ∑ k, Ind τ j (i, k) * G p w r j τ i k := by
    unfold E
    refine sum_le_sum (fun τ _ => mul_le_mul_of_nonneg_left ?_ (hμ.1 τ))
    rw [sum_ind]; exact Cslot_le_G p w r hp τ j
  have s2 : ∑ τ, μ τ * ∑ i, ∑ k, Ind τ j (i, k) * G p w r j τ i k =
      ∑ i, ∑ k, ∑ τ, μ τ * (Ind τ j (i, k) * G p w r j τ i k) := by
    simp_rw [mul_sum]; rw [sum_comm]; refine sum_congr rfl (fun i _ => ?_); rw [sum_comm]
  rw [s2] at s1
  refine s1.trans ?_
  unfold Cbar
  rw [mul_sum]
  refine sum_le_sum (fun i _ => ?_)
  rw [mul_sum]
  refine sum_le_sum (fun k _ => ?_)
  refine (slot_bound p w r hp hr a ha μ hμ j i k).trans ?_
  have hS : 0 ≤ ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j),
      a i k j' * p i j' := sum_nonneg (fun _ _ => mul_nonneg (ha0 _ _ _) (hp _ _).le)
  have h1 := ha0 i k j
  have h2 := hp i j
  have h3 : 0 ≤ a i k j * a i k j * p i j := by positivity
  have h4 : 0 ≤ a i k j * ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j),
      a i k j' * p i j' := mul_nonneg h1 hS
  nlinarith

theorem part2 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (a : Fin m → Fin n → Fin n → ℝ) (ha : CQPFeasible p r a)
    (μ : (Fin n → Fin m × Fin n) → ℝ) (hμ : IsPairwiseRounding a μ) :
    E μ (fun τ => ∑ j, w j * Cslot p w r τ j) ≤ 2 * ZCQP p w r a := by
  have e : E μ (fun τ => ∑ j, w j * Cslot p w r τ j) = ∑ j, w j * E μ (fun τ => Cslot p w r τ j) := by
    unfold E; simp_rw [mul_sum]; rw [sum_comm]
    exact sum_congr rfl (fun j _ => sum_congr rfl (fun τ _ => by ring))
  rw [e]; unfold ZCQP; rw [mul_sum]
  refine sum_le_sum (fun j _ => ?_)
  have := mul_le_mul_of_nonneg_left (E_Cslot_le p w r hp hr a ha μ hμ j) (hw j)
  linarith

theorem rho_zero_le {m n : ℕ} (r : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (h : 0 < n) :
    rho r i ⟨0, h⟩ ≤ r i j := by
  rw [← rho_exists r i j]; exact rho_mono r i (Fin.le_iff_val_le_val.2 (Nat.zero_le _))

noncomputable def Mb {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n) : ℝ :=
  ∑ j, |SkutellaCQP.RelDates.compl p S j| + ∑ i, ∑ k, |rho r i k|

theorem compl_le_Mb {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (j : Fin n) : SkutellaCQP.RelDates.compl p S j ≤ Mb p r S := by
  have h1 : |SkutellaCQP.RelDates.compl p S j| ≤ ∑ j, |SkutellaCQP.RelDates.compl p S j| :=
    single_le_sum (f := fun j => |SkutellaCQP.RelDates.compl p S j|) (fun _ _ => abs_nonneg _)
      (mem_univ j)
  have h2 : 0 ≤ ∑ i, ∑ k, |rho r i k| := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _))
  unfold Mb; linarith [le_abs_self (SkutellaCQP.RelDates.compl p S j)]

theorem rho_le_Mb {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) (k : Fin n) : rho r i k ≤ Mb p r S := by
  have h1 : |rho r i k| ≤ ∑ k, |rho r i k| :=
    single_le_sum (f := fun k => |rho r i k|) (fun _ _ => abs_nonneg _) (mem_univ k)
  have h1' : ∑ k, |rho r i k| ≤ ∑ i, ∑ k, |rho r i k| :=
    single_le_sum (f := fun i => ∑ k, |rho r i k|) (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _))
      (mem_univ i)
  have h2 : 0 ≤ ∑ j, |SkutellaCQP.RelDates.compl p S j| := sum_nonneg (fun _ _ => abs_nonneg _)
  unfold Mb; linarith [le_abs_self (rho r i k)]

noncomputable def Rr {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) (t : ℕ) : ℝ :=
  if h : t < n then rho r i ⟨t, h⟩ else Mb p r S

theorem Rr_mono {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) : Monotone (Rr p r S i) := by
  intro a b hab
  unfold Rr
  by_cases ha : a < n
  · by_cases hb : b < n
    · rw [dif_pos ha, dif_pos hb]; exact rho_mono r i (Fin.mk_le_mk.2 hab)
    · rw [dif_pos ha, dif_neg hb]; exact rho_le_Mb p r S i _
  · have hb : ¬ b < n := by omega
    rw [dif_neg ha, dif_neg hb]

theorem Rr_le_Mb {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) (t : ℕ) : Rr p r S i t ≤ Mb p r S := by
  unfold Rr; split_ifs
  · exact rho_le_Mb p r S i _
  · exact le_refl _

theorem Rr_fin {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) (k : Fin n) : Rr p r S i k.val = rho r i k := by
  unfold Rr; rw [dif_pos k.isLt]

def clampR (x lo hi : ℝ) : ℝ := min (max x lo) hi

theorem telescope (R : ℕ → ℝ) (hR : Monotone R) (F : ℝ → ℝ) (x : ℝ) (N : ℕ) :
    ∑ k ∈ range N, (F (clampR x (R k) (R (k + 1))) - F (R k)) =
      F (clampR x (R 0) (R N)) - F (R 0) := by
  induction N with
  | zero =>
    have : clampR x (R 0) (R 0) = R 0 := by unfold clampR; exact min_eq_right (le_max_right _ _)
    simp [this]
  | succ N ih =>
    rw [sum_range_succ, ih]
    have h0N : R 0 ≤ R N := hR (Nat.zero_le N)
    have hNN : R N ≤ R (N + 1) := hR (Nat.le_succ N)
    by_cases hx : x ≤ R N
    · have e1 : clampR x (R N) (R (N + 1)) = R N := by
        unfold clampR; rw [max_eq_right hx, min_eq_left hNN]
      have e2 : clampR x (R 0) (R N) = clampR x (R 0) (R (N + 1)) := by
        unfold clampR
        rw [min_eq_left (max_le hx h0N), min_eq_left (max_le (hx.trans hNN) (h0N.trans hNN))]
      rw [e1, e2]; ring
    · push Not at hx
      have e1 : clampR x (R 0) (R N) = R N := by
        unfold clampR; rw [max_eq_left (h0N.trans hx.le), min_eq_right hx.le]
      have e2 : clampR x (R N) (R (N + 1)) = clampR x (R 0) (R (N + 1)) := by
        unfold clampR; rw [max_eq_left hx.le, max_eq_left (h0N.trans hx.le)]
      rw [e1, e2]; ring

noncomputable def phi {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) (k : ℕ) (x : ℝ) : ℝ :=
  clampR x (Rr p r S i k) (Rr p r S i (k + 1))

theorem phi_mono {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) (k : ℕ) : Monotone (phi p r S i k) := by
  intro x y h
  unfold phi clampR
  exact min_le_min (max_le_max h le_rfl) le_rfl

theorem phi_low {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) (k : ℕ) (x : ℝ) (hx : x ≤ Rr p r S i k) : phi p r S i k x = Rr p r S i k := by
  unfold phi clampR
  rw [max_eq_right hx, min_eq_left (Rr_mono p r S i (Nat.le_succ k))]

theorem phi_high {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) (k : ℕ) (x : ℝ) (hx : Rr p r S i (k + 1) ≤ x) :
    phi p r S i k x = Rr p r S i (k + 1) := by
  unfold phi clampR
  rw [max_eq_left ((Rr_mono p r S i (Nat.le_succ k)).trans hx), min_eq_right hx]

theorem phi_sum {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (F : ℝ → ℝ) (i : Fin m) (x : ℝ) (hx0 : Rr p r S i 0 ≤ x) (hx1 : x ≤ Mb p r S) :
    ∑ k : Fin n, (F (phi p r S i k.val x) - F (Rr p r S i k.val)) = F x - F (Rr p r S i 0) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => F (phi p r S i k x) - F (Rr p r S i k)) n]
  unfold phi
  rw [telescope _ (Rr_mono p r S i) F x n]
  have hn : Rr p r S i n = Mb p r S := by unfold Rr; rw [dif_neg (lt_irrefl n)]
  have : clampR x (Rr p r S i 0) (Rr p r S i n) = x := by
    unfold clampR; rw [hn, max_eq_left hx0, min_eq_left hx1]
  rw [this]

/-- Disjoint intervals `[s t, c t)` inside `[A, X]`: their `g`-lengths add up to at most
`g X - g A` for monotone `g`. -/
theorem DL {ι : Type*} [DecidableEq ι] (s c : ι → ℝ) (g : ℝ → ℝ) (hg : Monotone g) (A : ℝ)
    (T : Finset ι) :
    (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → c t ≤ s t' ∨ c t' ≤ s t) →
    ∀ X, A ≤ X → (∀ t ∈ T, A ≤ s t ∧ s t < c t ∧ c t ≤ X) →
      ∑ t ∈ T, (g (c t) - g (s t)) ≤ g X - g A := by
  refine Finset.induction_on_max_value c T ?_ ?_
  · intro _ X hAX _
    simp only [sum_empty]
    linarith [hg hAX]
  · intro a T haT hmax ih hdisj X hAX hT
    have hdisjT : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → c t ≤ s t' ∨ c t' ≤ s t :=
      fun t ht t' ht' hne => hdisj t (mem_insert_of_mem ht) t' (mem_insert_of_mem ht') hne
    have ha := hT a (mem_insert_self a T)
    have hsub : ∀ t ∈ T, A ≤ s t ∧ s t < c t ∧ c t ≤ s a := by
      intro t ht
      have h1 := hT t (mem_insert_of_mem ht)
      refine ⟨h1.1, h1.2.1, ?_⟩
      have hne : t ≠ a := fun h => haT (h ▸ ht)
      rcases hdisj t (mem_insert_of_mem ht) a (mem_insert_self a T) hne with h | h
      · exact h
      · exfalso; have := hmax t ht; linarith [h1.2.1]
    have h2 := ih hdisjT (s a) ha.1 hsub
    rw [sum_insert haT]
    have h3 := hg ha.2.2
    linarith

noncomputable def ell {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) (k : Fin n) (j : Fin n) : ℝ :=
  if S.mach j = i then
    phi p r S i k.val (SkutellaCQP.RelDates.compl p S j) - phi p r S i k.val (S.start j)
  else 0

noncomputable def aS {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n) :
    Fin m → Fin n → Fin n → ℝ :=
  fun i k j => ell p r S i k j / p i j

theorem start_lt_compl {m n : ℕ} (p : Fin m → Fin n → ℝ) (hp : ∀ i j, 0 < p i j)
    (S : Sched m n) (j : Fin n) : S.start j < SkutellaCQP.RelDates.compl p S j := by
  unfold SkutellaCQP.RelDates.compl; linarith [hp (S.mach j) j]

theorem Rr0_le_start {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (hS : SFeasible p r S) (j : Fin n) : Rr p r S (S.mach j) 0 ≤ S.start j := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have e : Rr p r S (S.mach j) 0 = rho r (S.mach j) ⟨0, hn⟩ := by unfold Rr; rw [dif_pos hn]
  rw [e]; exact (rho_zero_le r (S.mach j) j hn).trans (hS.1 j)

theorem ell_nonneg {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (hp : ∀ i j, 0 < p i j)
    (S : Sched m n) (i : Fin m) (k j : Fin n) : 0 ≤ ell p r S i k j := by
  unfold ell; split_ifs
  · exact sub_nonneg.2 (phi_mono p r S i k.val (start_lt_compl p hp S j).le)
  · exact le_refl _

theorem ell_off {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (i : Fin m) (k j : Fin n) (h : S.mach j ≠ i) : ell p r S i k j = 0 := by
  unfold ell; rw [if_neg h]

theorem ell_on {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ) (S : Sched m n)
    (k j : Fin n) : ell p r S (S.mach j) k j =
      phi p r S (S.mach j) k.val (SkutellaCQP.RelDates.compl p S j) -
        phi p r S (S.mach j) k.val (S.start j) := by
  unfold ell; rw [if_pos rfl]

theorem sum_phi_F {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (S : Sched m n) (hS : SFeasible p r S) (F : ℝ → ℝ) (j : Fin n) :
    ∑ k : Fin n, (F (phi p r S (S.mach j) k.val (SkutellaCQP.RelDates.compl p S j)) -
      F (phi p r S (S.mach j) k.val (S.start j))) =
      F (SkutellaCQP.RelDates.compl p S j) - F (S.start j) := by
  have h0 := Rr0_le_start p r S hS j
  have hlt := start_lt_compl p hp S j
  have hC := compl_le_Mb p r S j
  have e1 := phi_sum p r S F (S.mach j) _ (h0.trans hlt.le) hC
  have e2 := phi_sum p r S F (S.mach j) _ h0 (hlt.le.trans hC)
  have e3 : ∑ k : Fin n, (F (phi p r S (S.mach j) k.val (SkutellaCQP.RelDates.compl p S j)) -
      F (phi p r S (S.mach j) k.val (S.start j))) =
      ∑ k : Fin n, (F (phi p r S (S.mach j) k.val (SkutellaCQP.RelDates.compl p S j)) -
        F (Rr p r S (S.mach j) k.val)) -
      ∑ k : Fin n, (F (phi p r S (S.mach j) k.val (S.start j)) - F (Rr p r S (S.mach j) k.val)) := by
    rw [← sum_sub_distrib]; exact sum_congr rfl (fun _ _ => by ring)
  rw [e3, e1, e2]; ring

theorem ell_sum {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (S : Sched m n) (hS : SFeasible p r S) (j : Fin n) :
    ∑ k, ell p r S (S.mach j) k j = p (S.mach j) j := by
  have := sum_phi_F p r hp S hS id j
  simp only [id] at this
  rw [sum_congr rfl (fun k _ => ell_on p r S k j), this]
  unfold SkutellaCQP.RelDates.compl; ring

theorem cqp_feasible {m n : ℕ} (p : Fin m → Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (S : Sched m n) (hS : SFeasible p r S) :
    CQPFeasible p r (aS p r S) := by
  refine ⟨⟨fun j => ?_, fun i k j hlt => ?_, fun i k j => ?_⟩, fun i k hk => ?_⟩
  · rw [sum_eq_single (S.mach j)]
    · unfold aS; rw [← sum_div, ell_sum p r hp S hS j]; exact div_self (hp _ _).ne'
    · intro i _ hi
      refine sum_eq_zero (fun k _ => ?_)
      unfold aS; rw [ell_off p r S i k j (Ne.symm hi), zero_div]
    · intro h; exact absurd (mem_univ _) h
  · unfold aS
    by_cases hm : S.mach j = i
    · subst hm
      set l := (Tuple.sort (r (S.mach j))).symm j with hl
      have hrl : rho r (S.mach j) l = r (S.mach j) j := rho_exists r (S.mach j) j
      have hkl : k < l := by
        by_contra hc; push Not at hc
        have := rho_mono r (S.mach j) hc
        linarith
      have hk1 : k.val + 1 < n := by have := l.isLt; have : k.val < l.val := hkl; omega
      have hR : Rr p r S (S.mach j) (k.val + 1) ≤ S.start j := by
        unfold Rr; rw [dif_pos hk1]
        have : rho r (S.mach j) ⟨k.val + 1, hk1⟩ ≤ rho r (S.mach j) l :=
          rho_mono r (S.mach j) (Fin.le_iff_val_le_val.2
            (show k.val + 1 ≤ l.val by have : k.val < l.val := hkl; omega))
        linarith [hS.1 j]
      rw [ell_on, phi_high p r S _ _ _ hR,
        phi_high p r S _ _ _ (hR.trans (start_lt_compl p hp S j).le)]
      simp
    · rw [ell_off p r S i k j hm, zero_div]
  · exact div_nonneg (ell_nonneg p r hp S i k j) (hp i j).le
  · have e : ∑ j, aS p r S i k j * p i j = ∑ j ∈ univ.filter (fun j => S.mach j = i),
        (phi p r S i k.val (SkutellaCQP.RelDates.compl p S j) - phi p r S i k.val (S.start j)) := by
      rw [sum_filter]
      refine sum_congr rfl (fun j _ => ?_)
      unfold aS; rw [div_mul_cancel₀ _ (hp i j).ne']
      unfold ell; rfl
    rw [e]
    have hn : 0 < n := Nat.zero_lt_of_lt k.isLt
    have hA : Rr p r S i 0 ≤ Mb p r S := Rr_le_Mb p r S i 0
    have hDL := DL (fun j => S.start j) (fun j => SkutellaCQP.RelDates.compl p S j)
      (phi p r S i k.val) (phi_mono p r S i k.val) (Rr p r S i 0)
      (univ.filter (fun j => S.mach j = i)) ?_ (Mb p r S) hA ?_
    · refine hDL.trans (le_of_eq ?_)
      rw [phi_high p r S i k.val _ (Rr_le_Mb p r S i _),
        phi_low p r S i k.val _ (Rr_mono p r S i (Nat.zero_le _))]
      unfold Rr; rw [dif_pos hk, dif_pos k.isLt]
    · intro t ht t' ht' hne
      rw [mem_filter] at ht ht'
      exact hS.2 t t' hne (ht.2.trans ht'.2.symm)
    · intro t ht
      rw [mem_filter] at ht
      refine ⟨?_, start_lt_compl p hp S t, compl_le_Mb p r S t⟩
      have := Rr0_le_start p r S hS t
      rw [ht.2] at this; exact this

theorem per_i {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (S : Sched m n) (hS : SFeasible p r S) (j : Fin n) (i : Fin m) :
    w j * ∑ k, aS p r S i k j * (rho r i k + (1 + aS p r S i k j) / 2 * p i j +
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), aS p r S i k j' * p i j') +
    ∑ k, w j / p i j * ell p r S i k j * (phi p r S i k.val (S.start j) - rho r i k -
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), ell p r S i k j') =
    if S.mach j = i then w j * SkutellaCQP.RelDates.compl p S j else 0 := by
  have hA : ∀ k, ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j),
      aS p r S i k j' * p i j' =
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), ell p r S i k j' :=
    fun k => sum_congr rfl (fun j' _ => by unfold aS; rw [div_mul_cancel₀ _ (hp i j').ne'])
  simp only [hA]
  by_cases hm : S.mach j = i
  · subst hm
    rw [if_pos rfl]
    have hp0 : p (S.mach j) j ≠ 0 := (hp _ _).ne'
    have key : ∀ k : Fin n, w j * (aS p r S (S.mach j) k j * (rho r (S.mach j) k +
        (1 + aS p r S (S.mach j) k j) / 2 * p (S.mach j) j +
        ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w (S.mach j) j' j),
          ell p r S (S.mach j) k j')) +
        w j / p (S.mach j) j * ell p r S (S.mach j) k j *
          (phi p r S (S.mach j) k.val (S.start j) - rho r (S.mach j) k -
          ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w (S.mach j) j' j),
            ell p r S (S.mach j) k j') =
        w j / 2 * ell p r S (S.mach j) k j + w j / p (S.mach j) j / 2 *
          (phi p r S (S.mach j) k.val (SkutellaCQP.RelDates.compl p S j) ^ 2 -
            phi p r S (S.mach j) k.val (S.start j) ^ 2) := by
      intro k
      have hL := ell_on p r S k j
      have ha : aS p r S (S.mach j) k j = ell p r S (S.mach j) k j / p (S.mach j) j := rfl
      rw [ha, hL]
      field_simp
      ring
    rw [mul_sum, ← sum_add_distrib, sum_congr rfl (fun k _ => key k), sum_add_distrib, ← mul_sum,
      ← mul_sum, ell_sum p r hp S hS j]
    have hsq := sum_phi_F p r hp S hS (fun x => x ^ 2) j
    rw [hsq]
    unfold SkutellaCQP.RelDates.compl
    field_simp
    ring
  · rw [if_neg hm]
    have h0 : ∀ k, ell p r S i k j = 0 := fun k => ell_off p r S i k j hm
    have h1 : ∀ k, aS p r S i k j = 0 := fun k => by unfold aS; rw [h0 k, zero_div]
    simp [h0, h1]

theorem perj {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (S : Sched m n) (hS : SFeasible p r S) (j : Fin n) :
    w j * SkutellaCQP.RelDates.compl p S j - w j * Cbar p w r (aS p r S) j =
    ∑ i, ∑ k, w j / p i j * ell p r S i k j * (phi p r S i k.val (S.start j) - rho r i k -
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), ell p r S i k j') := by
  have h := sum_congr rfl (fun i (_ : i ∈ univ) => per_i p w r hp S hS j i)
  rw [sum_ite_eq univ (S.mach j), if_pos (mem_univ _), sum_add_distrib, ← mul_sum] at h
  unfold Cbar
  linarith

theorem Dnonneg {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (S : Sched m n) (hS : SFeasible p r S)
    (i : Fin m) (k : Fin n) :
    0 ≤ ∑ j, w j / p i j * ell p r S i k j * (phi p r S i k.val (S.start j) - rho r i k -
      ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), ell p r S i k j') := by
  have hL0 : ∀ j, 0 ≤ ell p r S i k j := fun j => ell_nonneg p r hp S i k j
  have hc0 : ∀ j, 0 ≤ w j / p i j := fun j => div_nonneg (hw j) (hp i j).le
  have hB : ∀ j, ∑ j', (if S.mach j' = i ∧ SkutellaCQP.RelDates.compl p S j' ≤ S.start j then
      w j / p i j * ell p r S i k j * ell p r S i k j' else 0) ≤
      w j / p i j * ell p r S i k j * (phi p r S i k.val (S.start j) - rho r i k) := by
    intro j
    by_cases hm : S.mach j = i
    · rw [← sum_filter, ← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hc0 j) (hL0 j))
      have e : ∑ j' ∈ univ.filter (fun j' => S.mach j' = i ∧
          SkutellaCQP.RelDates.compl p S j' ≤ S.start j), ell p r S i k j' =
          ∑ j' ∈ univ.filter (fun j' => S.mach j' = i ∧
          SkutellaCQP.RelDates.compl p S j' ≤ S.start j),
          (phi p r S i k.val (SkutellaCQP.RelDates.compl p S j') - phi p r S i k.val (S.start j')) :=
        sum_congr rfl (fun j' hj' => by rw [mem_filter] at hj'; unfold ell; rw [if_pos hj'.2.1])
      rw [e]
      have hA : Rr p r S i 0 ≤ S.start j := by
        have := Rr0_le_start p r S hS j; rwa [hm] at this
      have hDL := DL (fun j => S.start j) (fun j => SkutellaCQP.RelDates.compl p S j)
        (phi p r S i k.val) (phi_mono p r S i k.val) (Rr p r S i 0)
        (univ.filter (fun j' => S.mach j' = i ∧ SkutellaCQP.RelDates.compl p S j' ≤ S.start j))
        ?_ (S.start j) hA ?_
      · refine hDL.trans (le_of_eq ?_)
        rw [phi_low p r S i k.val _ (Rr_mono p r S i (Nat.zero_le _)), Rr_fin]
      · intro t ht t' ht' hne
        rw [mem_filter] at ht ht'
        exact hS.2 t t' hne (ht.2.1.trans ht'.2.1.symm)
      · intro t ht
        rw [mem_filter] at ht
        refine ⟨?_, start_lt_compl p hp S t, ht.2.2⟩
        have := Rr0_le_start p r S hS t
        rwa [ht.2.1] at this
    · have : ell p r S i k j = 0 := ell_off p r S i k j hm
      simp [this]
  have hsym := sym_le
    (fun j j' => if SkutellaCQP.NoRel.prec p w i j' j then
      w j / p i j * ell p r S i k j * ell p r S i k j' else 0)
    (fun j j' => if S.mach j' = i ∧ SkutellaCQP.RelDates.compl p S j' ≤ S.start j then
      w j / p i j * ell p r S i k j * ell p r S i k j' else 0) ?_
  · have e1 : ∀ j, w j / p i j * ell p r S i k j * (phi p r S i k.val (S.start j) - rho r i k -
        ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), ell p r S i k j') =
        w j / p i j * ell p r S i k j * (phi p r S i k.val (S.start j) - rho r i k) -
        ∑ j', (if SkutellaCQP.NoRel.prec p w i j' j then
          w j / p i j * ell p r S i k j * ell p r S i k j' else 0) := by
      intro j
      rw [← sum_filter, ← mul_sum]; ring
    rw [sum_congr rfl (fun j _ => e1 j), sum_sub_distrib]
    have e2 := sum_le_sum (fun j (_ : j ∈ univ) => hB j)
    linarith
  · intro j j'
    have hLL := mul_nonneg (hL0 j) (hL0 j')
    by_cases hz : ell p r S i k j = 0 ∨ ell p r S i k j' = 0
    · rcases hz with hz | hz <;> simp [hz]
    · push Not at hz
      obtain ⟨hz1, hz2⟩ := hz
      have hm1 : S.mach j = i := by
        by_contra h; exact hz1 (ell_off p r S i k j h)
      have hm2 : S.mach j' = i := by
        by_contra h; exact hz2 (ell_off p r S i k j' h)
      have e12 : ∀ x y, w x / p i x * ell p r S i k x * ell p r S i k y =
          w x / p i x * (ell p r S i k x * ell p r S i k y) := fun x y => by ring
      have eLL : ell p r S i k j' * ell p r S i k j = ell p r S i k j * ell p r S i k j' := by ring
      simp only [e12, eLL]
      have g1 : 0 ≤ (if S.mach j' = i ∧ SkutellaCQP.RelDates.compl p S j' ≤ S.start j then
          w j / p i j * (ell p r S i k j * ell p r S i k j') else 0) := by
        split_ifs
        · exact mul_nonneg (hc0 j) hLL
        · exact le_refl _
      have g2 : 0 ≤ (if S.mach j = i ∧ SkutellaCQP.RelDates.compl p S j ≤ S.start j' then
          w j' / p i j' * (ell p r S i k j * ell p r S i k j') else 0) := by
        split_ifs
        · exact mul_nonneg (hc0 j') hLL
        · exact le_refl _
      by_cases hjj : j = j'
      · subst hjj
        rw [if_neg (prec_irrefl p w i j)]
        linarith
      · rcases hS.2 j j' hjj (hm1.trans hm2.symm) with hb | hb
        · rw [if_pos (show S.mach j = i ∧ SkutellaCQP.RelDates.compl p S j ≤ S.start j' from ⟨hm1, hb⟩)] at g2 ⊢
          rcases prec_total p w i j j' hjj with hpr | hpr
          · rw [if_neg (prec_asymm p w i j j' hpr), if_pos hpr]; linarith
          · rw [if_pos hpr, if_neg (prec_asymm p w i j' j hpr)]
            have hc : w j / p i j ≤ w j' / p i j' := by
              rw [div_le_div_iff₀ (hp i j) (hp i j')]; linarith [prec_le p w i j' j hpr]
            have := mul_le_mul_of_nonneg_right hc hLL
            linarith
        · rw [if_pos (show S.mach j' = i ∧ SkutellaCQP.RelDates.compl p S j' ≤ S.start j from ⟨hm2, hb⟩)] at g1 ⊢
          rcases prec_total p w i j j' hjj with hpr | hpr
          · rw [if_neg (prec_asymm p w i j j' hpr), if_pos hpr]
            have hc : w j' / p i j' ≤ w j / p i j := by
              rw [div_le_div_iff₀ (hp i j') (hp i j)]; linarith [prec_le p w i j j' hpr]
            have := mul_le_mul_of_nonneg_right hc hLL
            linarith
          · rw [if_pos hpr, if_neg (prec_asymm p w i j' j hpr)]; linarith

theorem part3 {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (S : Sched m n) (hS : SFeasible p r S) :
    ∃ a : Fin m → Fin n → Fin n → ℝ, CQPFeasible p r a ∧ ZCQP p w r a ≤ sval p w S := by
  refine ⟨aS p r S, cqp_feasible p r hp S hS, ?_⟩
  have h : sval p w S - ZCQP p w r (aS p r S) =
      ∑ i, ∑ k, ∑ j, w j / p i j * ell p r S i k j * (phi p r S i k.val (S.start j) - rho r i k -
        ∑ j' ∈ univ.filter (fun j' => SkutellaCQP.NoRel.prec p w i j' j), ell p r S i k j') := by
    unfold sval ZCQP
    rw [← sum_sub_distrib, sum_congr rfl (fun j _ => perj p w r hp S hS j), sum_comm]
    refine sum_congr rfl (fun i _ => ?_)
    rw [sum_comm]
  have h2 := sum_nonneg (fun i (_ : i ∈ univ) =>
    sum_nonneg (fun k (_ : k ∈ univ) => Dnonneg p w r hp hw S hS i k))
  linarith

end SkutAuxdd60

open SkutellaCQP.RelDates Finset in
theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j) :
    (∀ τ : Fin n → Fin m × Fin n, SlotFeasible r τ →
        SFeasible p r (schedOf p w r τ) ∧ ∀ j, compl p (schedOf p w r τ) j = Cslot p w r τ j) ∧
      (∀ a : Fin m → Fin n → Fin n → ℝ, CQPFeasible p r a →
        ∀ μ : (Fin n → Fin m × Fin n) → ℝ, IsPairwiseRounding a μ →
          E μ (fun τ => ∑ j, w j * Cslot p w r τ j) ≤ 2 * ZCQP p w r a) ∧
      (∀ S : Sched m n, SFeasible p r S →
        ∃ a : Fin m → Fin n → Fin n → ℝ, CQPFeasible p r a ∧ ZCQP p w r a ≤ sval p w S) := by
  exact ⟨fun τ hτ => SkutAuxdd60.part1 p w r hp τ hτ,
    fun a ha μ hμ => SkutAuxdd60.part2 p w r hp hw hr a ha μ hμ,
    fun S hS => SkutAuxdd60.part3 p w r hp hw S hS⟩
