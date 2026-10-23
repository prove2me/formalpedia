-- Prove2me | solution 1 for VehicleSharePricing.Static.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T05:16:13.514704+00:00
-- url     : https://prove2.me/submissions/5f5ea788-1b74-4a8a-988c-636e10700829

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_Model
import Definitions.Def_VehicleSharePricing_Static_Availability
import Definitions.Def_VehicleSharePricing_Static_BoundSeq

set_option autoImplicit false

namespace VSPAux

open Finset VehicleSharePricing.Static

section PF

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma mem_popStates (K : ℕ) (x : S → ℕ) : x ∈ popStates S K ↔ ∑ s, x s = K := by
  unfold popStates
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun t => ?_, h⟩
    have := Finset.single_le_sum (f := x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    omega

lemma sum_single_nat (s : S) (n : ℕ) : ∑ t, (Pi.single s n : S → ℕ) t = n := by
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ s) h

lemma sum_shift (K : ℕ) (s : S) (f : (S → ℕ) → ℝ) :
    ∑ x ∈ (popStates S (K + 1)).filter (fun x => 1 ≤ x s), f x =
      ∑ y ∈ popStates S K, f (y + Pi.single s 1) := by
  symm
  apply Finset.sum_nbij' (fun y => y + Pi.single s 1) (fun x => x - Pi.single s 1)
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, mem_popStates] at hy ⊢
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, sum_single_nat, hy]
    · simp
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, mem_popStates] at hx ⊢
    have h1 : (x - Pi.single s 1) + Pi.single s 1 = x := by
      funext t
      by_cases ht : t = s
      · subst ht; simp; omega
      · simp [Pi.single_apply, ht]
    have h2 := congrArg (fun z : S → ℕ => ∑ t, z t) h1
    simp only [Pi.add_apply] at h2
    rw [Finset.sum_add_distrib, sum_single_nat] at h2
    omega
  · intro y _
    funext t
    by_cases ht : t = s
    · subst ht; simp
    · simp [Pi.single_apply, ht]
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx
    funext t
    by_cases ht : t = s
    · subst ht; simp; omega
    · simp [Pi.single_apply, ht]
  · intro y _
    rfl

lemma weight_compl (ρ : S → ℝ) (isIS : S → Bool) (y : S → ℕ) (s : S) :
    ∏ t ∈ ({s}ᶜ : Finset S), (if isIS t then ρ t ^ (y + Pi.single s 1 : S → ℕ) t /
        (((y + Pi.single s 1 : S → ℕ) t).factorial : ℝ) else ρ t ^ (y + Pi.single s 1 : S → ℕ) t) =
      ∏ t ∈ ({s}ᶜ : Finset S), (if isIS t then ρ t ^ y t / ((y t).factorial : ℝ)
        else ρ t ^ y t) := by
  apply Finset.prod_congr rfl
  intro t ht
  have : t ≠ s := by simpa using ht
  simp [Pi.single_apply, this]

lemma weight_shift_single (ρ : S → ℝ) (isIS : S → Bool) (y : S → ℕ) (s : S)
    (h : isIS s = false) :
    pfWeight ρ isIS (y + Pi.single s 1) = ρ s * pfWeight ρ isIS y := by
  unfold pfWeight
  rw [Fintype.prod_eq_mul_prod_compl s, weight_compl,
    Fintype.prod_eq_mul_prod_compl s (fun t => if isIS t then ρ t ^ y t / ((y t).factorial : ℝ)
      else ρ t ^ y t)]
  simp only [h, Pi.add_apply, Pi.single_eq_same]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

lemma weight_shift_IS (ρ : S → ℝ) (isIS : S → Bool) (y : S → ℕ) (s : S)
    (h : isIS s = true) :
    pfWeight ρ isIS (y + Pi.single s 1) * ((y s : ℝ) + 1) = ρ s * pfWeight ρ isIS y := by
  unfold pfWeight
  rw [Fintype.prod_eq_mul_prod_compl s, weight_compl,
    Fintype.prod_eq_mul_prod_compl s (fun t => if isIS t then ρ t ^ y t / ((y t).factorial : ℝ)
      else ρ t ^ y t)]
  simp only [h, Pi.add_apply, Pi.single_eq_same, ↓reduceIte]
  rw [Nat.factorial_succ]
  push_cast
  have hf : ((y s).factorial : ℝ) ≠ 0 := by positivity
  have hy : ((y s : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Mean-population sum `∑_x x_s w(x)`. -/
noncomputable def Lsum (ρ : S → ℝ) (isIS : S → Bool) (K : ℕ) (s : S) : ℝ :=
  ∑ x ∈ popStates S K, (x s : ℝ) * pfWeight ρ isIS x

lemma Lsum_eq_filter (ρ : S → ℝ) (isIS : S → Bool) (K : ℕ) (s : S) :
    Lsum ρ isIS K s = ∑ x ∈ (popStates S K).filter (fun x => 1 ≤ x s),
      (x s : ℝ) * pfWeight ρ isIS x := by
  unfold Lsum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with h
  · rfl
  · have : x s = 0 := by omega
    simp [this]

lemma Lsum_zero (ρ : S → ℝ) (isIS : S → Bool) (s : S) : Lsum ρ isIS 0 s = 0 := by
  unfold Lsum
  apply Finset.sum_eq_zero
  intro x hx
  rw [mem_popStates] at hx
  have := Finset.single_le_sum (f := x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  have h0 : x s = 0 := by omega
  simp [h0]

lemma Lsum_succ_IS (ρ : S → ℝ) (isIS : S → Bool) (K : ℕ) (s : S) (h : isIS s = true) :
    Lsum ρ isIS (K + 1) s = ρ s * pfNormConst ρ isIS K := by
  rw [Lsum_eq_filter, sum_shift]
  unfold pfNormConst
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have := weight_shift_IS ρ isIS y s h
  simp only [Pi.add_apply, Pi.single_eq_same]
  push_cast
  rw [← this]
  ring

lemma Lsum_succ_single (ρ : S → ℝ) (isIS : S → Bool) (K : ℕ) (s : S) (h : isIS s = false) :
    Lsum ρ isIS (K + 1) s = ρ s * (Lsum ρ isIS K s + pfNormConst ρ isIS K) := by
  rw [Lsum_eq_filter, sum_shift]
  unfold pfNormConst Lsum
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [weight_shift_single ρ isIS y s h]
  simp only [Pi.add_apply, Pi.single_eq_same]
  push_cast
  ring

lemma sum_Lsum (ρ : S → ℝ) (isIS : S → Bool) (K : ℕ) :
    ∑ s, Lsum ρ isIS K s = (K : ℝ) * pfNormConst ρ isIS K := by
  unfold Lsum pfNormConst
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_mul]
  rw [mem_popStates] at hx
  congr 1
  exact_mod_cast hx

lemma busy_eq (ρ : S → ℝ) (isIS : S → Bool) (K : ℕ) (s : S) :
    pfBusyProb ρ isIS K s =
      (∑ x ∈ (popStates S K).filter (fun x => 1 ≤ x s), pfWeight ρ isIS x) /
        pfNormConst ρ isIS K := by
  unfold pfBusyProb pfProb
  rw [Finset.sum_div]

lemma busy_zero (ρ : S → ℝ) (isIS : S → Bool) (s : S) : pfBusyProb ρ isIS 0 s = 0 := by
  rw [busy_eq]
  have : ∑ x ∈ (popStates S 0).filter (fun x => 1 ≤ x s), pfWeight ρ isIS x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter, mem_popStates] at hx
    have := Finset.single_le_sum (f := x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    omega
  rw [this, zero_div]

lemma busy_succ_single (ρ : S → ℝ) (isIS : S → Bool) (K : ℕ) (s : S) (h : isIS s = false) :
    pfBusyProb ρ isIS (K + 1) s = ρ s * pfNormConst ρ isIS K / pfNormConst ρ isIS (K + 1) := by
  rw [busy_eq, sum_shift]
  congr 1
  unfold pfNormConst
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact weight_shift_single ρ isIS y s h

lemma normConst_pos (ρ : S → ℝ) (isIS : S → Bool) (hρ : ∀ s, 0 ≤ ρ s) (s0 : S)
    (hs0 : isIS s0 = false) (hpos : 0 < ρ s0) (K : ℕ) : 0 < pfNormConst ρ isIS K := by
  unfold pfNormConst
  apply Finset.sum_pos'
  · intro x _
    unfold pfWeight
    apply Finset.prod_nonneg
    intro t _
    have := hρ t
    split_ifs <;> positivity
  · refine ⟨Pi.single s0 K, ?_, ?_⟩
    · rw [mem_popStates]; exact sum_single_nat s0 K
    · unfold pfWeight
      rw [Fintype.prod_eq_mul_prod_compl s0]
      have hc : ∏ t ∈ ({s0}ᶜ : Finset S), (if isIS t then ρ t ^ (Pi.single s0 K : S → ℕ) t /
          (((Pi.single s0 K : S → ℕ) t).factorial : ℝ) else ρ t ^ (Pi.single s0 K : S → ℕ) t)
            = 1 := by
        apply Finset.prod_eq_one
        intro t ht
        have : t ≠ s0 := by simpa using ht
        simp [Pi.single_apply, this]
      rw [hc]
      simp [hs0]
      positivity

end PF

/-! ### The bound sequence -/

section B

variable (N : ℕ)

lemma Bseq_zero (ρ : ℝ) (K : ℕ) : Bseq N ρ K 0 = 0 := by
  rw [Bseq]

lemma Bseq_succ (ρ : ℝ) (K i : ℕ) :
    Bseq N ρ K (i + 1) = (K : ℝ) / ((N : ℝ) + K - 1 + ρ * (1 - Bseq N ρ (K - 1) i)) := by
  rw [Bseq]

lemma Bseq_mem (hN : 1 ≤ N) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ i K, 0 ≤ Bseq N ρ K i ∧ Bseq N ρ K i ≤ 1 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  intro i
  induction i with
  | zero => intro K; simp [Bseq_zero]
  | succ i ih =>
    intro K
    rw [Bseq_succ]
    obtain ⟨h0, h1⟩ := ih (K - 1)
    have hm : 0 ≤ ρ * (1 - Bseq N ρ (K - 1) i) := mul_nonneg hρ (by linarith)
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp
    · have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have hd : 0 < (N : ℝ) + K - 1 + ρ * (1 - Bseq N ρ (K - 1) i) := by linarith
      refine ⟨div_nonneg (by linarith) hd.le, ?_⟩
      rw [div_le_one hd]
      linarith

lemma Bseq_mono_succ (hN : 1 ≤ N) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ i K, Bseq N ρ K i ≤ Bseq N ρ K (i + 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  intro i
  induction i with
  | zero => intro K; rw [Bseq_zero]; exact (Bseq_mem N hN ρ hρ 1 K).1
  | succ i ih =>
    intro K
    rw [Bseq_succ, Bseq_succ]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp
    · have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have hb := Bseq_mem N hN ρ hρ (i + 1) (K - 1)
      have hle := ih (K - 1)
      have hm : 0 ≤ ρ * (1 - Bseq N ρ (K - 1) (i + 1)) := mul_nonneg hρ (by linarith [hb.2])
      apply div_le_div_of_nonneg_left (by linarith) (by linarith)
      have := mul_le_mul_of_nonneg_left (show 1 - Bseq N ρ (K - 1) (i + 1) ≤
        1 - Bseq N ρ (K - 1) i by linarith) hρ
      linarith

lemma Bseq_strict (hN : 1 ≤ N) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ i K, i + 1 ≤ K → Bseq N ρ K i < Bseq N ρ K (i + 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  intro i
  induction i with
  | zero =>
    intro K hK
    rw [Bseq_zero, Bseq_succ, Bseq_zero]
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    apply div_pos (by linarith)
    linarith
  | succ i ih =>
    intro K hK
    rw [Bseq_succ, Bseq_succ]
    have hK' : (1 : ℝ) ≤ K := by
      have : 1 ≤ K := by omega
      exact_mod_cast this
    have hb := Bseq_mem N hN ρ hρ.le (i + 1) (K - 1)
    have hlt := ih (K - 1) (by omega)
    have hm : 0 ≤ ρ * (1 - Bseq N ρ (K - 1) (i + 1)) := mul_nonneg hρ.le (by linarith [hb.2])
    apply div_lt_div_of_pos_left (by linarith) (by linarith)
    have := mul_lt_mul_of_pos_left (show 1 - Bseq N ρ (K - 1) (i + 1) <
      1 - Bseq N ρ (K - 1) i by linarith) hρ
    linarith

lemma Bseq_anti (hN : 1 ≤ N) (ρ₁ ρ₂ : ℝ) (h₁ : 0 ≤ ρ₁) (h₁₂ : ρ₁ ≤ ρ₂) :
    ∀ i K, Bseq N ρ₂ K i ≤ Bseq N ρ₁ K i := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h₂ : 0 ≤ ρ₂ := le_trans h₁ h₁₂
  intro i
  induction i with
  | zero => intro K; simp [Bseq_zero]
  | succ i ih =>
    intro K
    rw [Bseq_succ, Bseq_succ]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp
    · have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have hb1 := Bseq_mem N hN ρ₁ h₁ i (K - 1)
      have hb2 := Bseq_mem N hN ρ₂ h₂ i (K - 1)
      have hle := ih (K - 1)
      have hm : 0 ≤ ρ₁ * (1 - Bseq N ρ₁ (K - 1) i) := mul_nonneg h₁ (by linarith [hb1.2])
      apply div_le_div_of_nonneg_left (by linarith) (by linarith)
      have := mul_le_mul h₁₂ (show 1 - Bseq N ρ₁ (K - 1) i ≤ 1 - Bseq N ρ₂ (K - 1) i by linarith)
        (by linarith [hb1.2]) h₂
      linarith

end B

/-! ### The closed network of a static policy -/

section Net

variable {L : Type*} [Fintype L] [DecidableEq L]

lemma busy_inl_eq (ρ : Station L → ℝ) (c : ℝ) (hin : ∀ i, ρ (Sum.inl i) = c) (K : ℕ) (i j : L) :
    pfBusyProb ρ stationIsIS K (Sum.inl i) = pfBusyProb ρ stationIsIS K (Sum.inl j) := by
  rcases K with _ | K
  · rw [busy_zero, busy_zero]
  · rw [busy_succ_single ρ stationIsIS K (Sum.inl i) rfl,
      busy_succ_single ρ stationIsIS K (Sum.inl j) rfl, hin, hin]

lemma busy_recursion [Nonempty L] (ρ : Station L → ℝ) (c W : ℝ) (hρ : ∀ s, 0 ≤ ρ s)
    (hc : 0 < c) (hin : ∀ i, ρ (Sum.inl i) = c)
    (hW : ∑ p : L × L, ρ (Sum.inr p) = c * W) (i : L) (K : ℕ) :
    pfBusyProb ρ stationIsIS (K + 1) (Sum.inl i) *
      ((Fintype.card L : ℝ) + K + W * (1 - pfBusyProb ρ stationIsIS K (Sum.inl i))) = K + 1 := by
  have hGpos : ∀ n, 0 < pfNormConst ρ stationIsIS n := fun n =>
    normConst_pos ρ stationIsIS hρ (Sum.inl i) rfl (by rw [hin]; exact hc) n
  have hISs : ∀ n (p : L × L), Lsum ρ stationIsIS (n + 1) (Sum.inr p) =
      ρ (Sum.inr p) * pfNormConst ρ stationIsIS n := fun n p =>
    Lsum_succ_IS ρ stationIsIS n (Sum.inr p) rfl
  have hSs : ∀ n (j : L), Lsum ρ stationIsIS (n + 1) (Sum.inl j) =
      c * (Lsum ρ stationIsIS n (Sum.inl j) + pfNormConst ρ stationIsIS n) := fun n j => by
    rw [Lsum_succ_single ρ stationIsIS n (Sum.inl j) rfl, hin]
  have hIS : ∀ n, ∑ p : L × L, Lsum ρ stationIsIS (n + 1) (Sum.inr p) =
      c * W * pfNormConst ρ stationIsIS n := by
    intro n
    simp only [hISs]
    rw [← Finset.sum_mul, hW]
  have hAeq : ∑ j : L, Lsum ρ stationIsIS K (Sum.inl j) = K * pfNormConst ρ stationIsIS K -
      W * pfBusyProb ρ stationIsIS K (Sum.inl i) * pfNormConst ρ stationIsIS K := by
    have htot := sum_Lsum ρ (stationIsIS (L := L)) K
    rw [Fintype.sum_sum_type] at htot
    rcases K with _ | k
    · simp only [Lsum_zero, Finset.sum_const_zero, busy_zero]; simp
    · rw [hIS k] at htot
      rw [busy_succ_single ρ stationIsIS k (Sum.inl i) rfl, hin]
      have hne := (hGpos (k + 1)).ne'
      have e : W * (c * pfNormConst ρ stationIsIS k / pfNormConst ρ stationIsIS (k + 1)) *
          pfNormConst ρ stationIsIS (k + 1) = c * W * pfNormConst ρ stationIsIS k := by
        rw [mul_assoc, div_mul_cancel₀ _ hne]; ring
      rw [e]
      linarith
  have hkey : ((K : ℝ) + 1) * pfNormConst ρ stationIsIS (K + 1) =
      c * pfNormConst ρ stationIsIS K *
        ((Fintype.card L : ℝ) + K + W * (1 - pfBusyProb ρ stationIsIS K (Sum.inl i))) := by
    have htot := sum_Lsum ρ (stationIsIS (L := L)) (K + 1)
    rw [Fintype.sum_sum_type, hIS K] at htot
    simp only [hSs] at htot
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hAeq] at htot
    push_cast at htot
    linarith
  rw [busy_succ_single ρ stationIsIS K (Sum.inl i) rfl, hin]
  have := hGpos (K + 1)
  rw [div_mul_eq_mul_div, div_eq_iff this.ne']
  linarith

lemma busy_eq_Bseq [Nonempty L] (ρ : Station L → ℝ) (c W : ℝ) (hρ : ∀ s, 0 ≤ ρ s)
    (hc : 0 < c) (hin : ∀ i, ρ (Sum.inl i) = c) (hW0 : 0 ≤ W)
    (hW : ∑ p : L × L, ρ (Sum.inr p) = c * W) (i : L) :
    ∀ K, pfBusyProb ρ stationIsIS K (Sum.inl i) = Bseq (Fintype.card L) W K K := by
  have hN : 1 ≤ Fintype.card L := Fintype.card_pos
  have hN' : (1 : ℝ) ≤ Fintype.card L := by exact_mod_cast hN
  intro K
  induction K with
  | zero => rw [busy_zero, Bseq_zero]
  | succ K ih =>
    have hrec := busy_recursion ρ c W hρ hc hin hW i K
    rw [ih] at hrec
    rw [Bseq_succ]
    simp only [Nat.add_sub_cancel]
    have hb := Bseq_mem _ hN W hW0 K K
    have hm : 0 ≤ W * (1 - Bseq (Fintype.card L) W K K) := mul_nonneg hW0 (by linarith [hb.2])
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hd : (0 : ℝ) < (Fintype.card L : ℝ) + ((K + 1 : ℕ) : ℝ) - 1 +
        W * (1 - Bseq (Fintype.card L) W K K) := by push_cast; linarith
    rw [eq_div_iff hd.ne']
    push_cast
    have : (Fintype.card L : ℝ) + ((K : ℝ) + 1) - 1 + W * (1 - Bseq (Fintype.card L) W K K) =
        (Fintype.card L : ℝ) + K + W * (1 - Bseq (Fintype.card L) W K K) := by ring
    rw [this, hrec]

end Net

end VSPAux

open VehicleSharePricing.Static in
theorem solution {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (P : Instance L) (K : ℕ) (hK : 1 ≤ K) (Δ : ℝ) (hΔ : (K : ℝ) ≤ Δ)
    (qs : L → L → ℝ) (hopt : IsStaticOptimal P Δ qs) (hconn : InducesStronglyConnected P qs)
    (hRs : 0 < Rs P qs) (r : L → ℝ) (hr : IsTrafficSolution P qs r) :
    (∀ i : ℕ, 1 ≤ i → i ≤ K →
      R P qs r K / Rs P qs ≥ Bseq (Fintype.card L) (workload P qs) K i ∧
      Bseq (Fintype.card L) (workload P qs) K i ≥
        Bseq (Fintype.card L) (demandWorkload P) K i ∧
      Bseq (Fintype.card L) (demandWorkload P) K i ≥
        (K : ℝ) / ((Fintype.card L : ℝ) + (K : ℝ) - 1 + demandWorkload P)) ∧
    (∀ i : ℕ, 1 ≤ i → i + 1 ≤ K →
      Bseq (Fintype.card L) (demandWorkload P) K (i + 1) >
        Bseq (Fintype.card L) (demandWorkload P) K i) := by
  classical
  obtain ⟨⟨hbal, -, hq⟩, -⟩ := hopt
  obtain ⟨hrpos, htraf⟩ := hr
  have hN : 1 ≤ Fintype.card L := Fintype.card_pos
  -- nonnegativity of effective rates
  have he0 : ∀ i j, 0 ≤ effRate P qs i j := by
    intro i j
    unfold effRate
    rcases (P.demand_nonneg i j).lt_or_eq with h | h
    · exact mul_nonneg h.le (hq i j h).1
    · rw [← h, zero_mul]
  have hdiv0 : ∀ i j, 0 ≤ effRate P qs i j / P.rate i j := by
    intro i j
    rcases (P.demand_nonneg i j).lt_or_eq with h | h
    · exact div_nonneg (he0 i j) (P.rate_pos i j h).le
    · unfold effRate; rw [← h, zero_mul, zero_div]
  have hlampos : ∀ i, 0 < outRate P qs i := by
    intro i
    obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.mp (hconn i i)
    unfold outRate
    exact lt_of_lt_of_le hb
      (Finset.single_le_sum (f := fun j => effRate P qs i j) (fun j _ => he0 i j)
        (Finset.mem_univ b))
  -- the traffic solution is proportional to the out-rates
  set t : L → ℝ := fun j => r j / outRate P qs j with ht
  have htsum : ∀ i, ∑ j, t j * effRate P qs j i = t i * ∑ j, effRate P qs j i := by
    intro i
    have h1 := htraf i
    have h2 : ∑ j, effRate P qs j i = outRate P qs i := by
      have := hbal i
      unfold outRate effRate
      exact this.symm
    rw [h2]
    have h3 : t i * outRate P qs i = r i := by
      simp only [ht]; field_simp [(hlampos i).ne']
    rw [h3, ← h1]
    apply Finset.sum_congr rfl
    intro j _
    simp only [ht]
    ring
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ t Finset.univ_nonempty
  have hclaim : ∀ i, t i = t m → ∀ j, 0 < effRate P qs j i → t j = t m := by
    intro i hi j hj
    have hz : ∑ k, effRate P qs k i * (t m - t k) = 0 := by
      have := htsum i
      rw [hi] at this
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, mul_comm, ← this]
      simp only [mul_comm]
      ring
    have hnn : ∀ k ∈ Finset.univ, 0 ≤ effRate P qs k i * (t m - t k) := fun k _ =>
      mul_nonneg (he0 k i) (by linarith [hm k (Finset.mem_univ k)])
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz j (Finset.mem_univ j)
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hconst : ∀ a, t a = t m := by
    intro a
    have h : Relation.TransGen (fun a b => 0 < P.demand a b * qs a b) a m := hconn a m
    induction h using Relation.TransGen.head_induction_on with
    | single h => exact hclaim m rfl _ h
    | head h _ hc => exact hclaim _ hc _ h
  set c := t m with hcdef
  have hcpos : 0 < c := div_pos (hrpos m) (hlampos m)
  -- station loads
  set ρ := stationLoad P qs r with hρdef
  have hin : ∀ i, ρ (Sum.inl i) = c := fun i => hconst i
  have hinr : ∀ i j, ρ (Sum.inr (i, j)) = c * (effRate P qs i j / P.rate i j) := by
    intro i j
    show r i * effRate P qs i j / (outRate P qs i * P.rate i j) = _
    rw [mul_div_mul_comm]
    rw [show r i / outRate P qs i = c from hconst i]
  have hρ0 : ∀ s, 0 ≤ ρ s := by
    intro s
    rcases s with i | ⟨i, j⟩
    · rw [hin]; exact hcpos.le
    · rw [hinr]; exact mul_nonneg hcpos.le (hdiv0 i j)
  have hW : ∑ p : L × L, ρ (Sum.inr p) = c * workload P qs := by
    rw [Fintype.sum_prod_type]
    simp only [hinr]
    unfold workload effRate
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hW0 : 0 ≤ workload P qs := by
    unfold workload
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    exact hdiv0 i j
  -- availabilities
  set i0 : L := Classical.arbitrary L
  have hav : ∀ i, availability P qs r K i = Bseq (Fintype.card L) (workload P qs) K K := by
    intro i
    unfold availability
    rw [VSPAux.busy_inl_eq ρ c hin K i i0]
    exact VSPAux.busy_eq_Bseq ρ c (workload P qs) hρ0 hcpos hin hW0 hW i0 K
  have hratio : R P qs r K / Rs P qs = Bseq (Fintype.card L) (workload P qs) K K := by
    have : R P qs r K = Bseq (Fintype.card L) (workload P qs) K K * Rs P qs := by
      unfold R Rs
      simp only [hav]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [this, mul_div_assoc, div_self hRs.ne', mul_one]
  -- the demand workload
  have hTpos : 0 < totalDemand P := by
    obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.mp (P.strongly_connected i0 i0)
    unfold totalDemand
    have hin' : ∀ i, 0 ≤ ∑ j, P.demand i j := fun i =>
      Finset.sum_nonneg (fun j _ => P.demand_nonneg i j)
    exact lt_of_lt_of_le hb (le_trans
      (Finset.single_le_sum (f := fun j => P.demand i0 j) (fun j _ => P.demand_nonneg i0 j)
        (Finset.mem_univ b))
      (Finset.single_le_sum (f := fun i => ∑ j, P.demand i j) (fun i _ => hin' i)
        (Finset.mem_univ i0)))
  have hDW : demandWorkload P = ∑ i, ∑ j, P.demand i j / P.rate i j := by
    unfold demandWorkload invMeanTravel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_div_assoc, mul_div_mul_left _ _ hTpos.ne']
  have hdd0 : ∀ i j, 0 ≤ P.demand i j / P.rate i j := by
    intro i j
    rcases (P.demand_nonneg i j).lt_or_eq with h | h
    · exact div_nonneg h.le (P.rate_pos i j h).le
    · rw [← h, zero_div]
  have hDpos : 0 < demandWorkload P := by
    obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.mp (P.strongly_connected i0 i0)
    rw [hDW]
    have hin' : ∀ i, 0 ≤ ∑ j, P.demand i j / P.rate i j := fun i =>
      Finset.sum_nonneg (fun j _ => hdd0 i j)
    exact lt_of_lt_of_le (div_pos hb (P.rate_pos _ _ hb)) (le_trans
      (Finset.single_le_sum (f := fun j => P.demand i0 j / P.rate i0 j) (fun j _ => hdd0 i0 j)
        (Finset.mem_univ b))
      (Finset.single_le_sum (f := fun i => ∑ j, P.demand i j / P.rate i j) (fun i _ => hin' i)
        (Finset.mem_univ i0)))
  have hWle : workload P qs ≤ demandWorkload P := by
    rw [hDW]
    unfold workload
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    rcases (P.demand_nonneg i j).lt_or_eq with h | h
    · rw [mul_div_right_comm]
      exact mul_le_of_le_one_right (hdd0 i j) (hq i j h).2
    · rw [← h]; simp
  have hmonoW : Monotone (fun i => Bseq (Fintype.card L) (workload P qs) K i) :=
    monotone_nat_of_le_succ (fun n => VSPAux.Bseq_mono_succ _ hN _ hW0 n K)
  have hmonoD : Monotone (fun i => Bseq (Fintype.card L) (demandWorkload P) K i) :=
    monotone_nat_of_le_succ (fun n => VSPAux.Bseq_mono_succ _ hN _ hDpos.le n K)
  refine ⟨fun i hi hiK => ⟨?_, ?_, ?_⟩, fun i hi hiK => ?_⟩
  · rw [hratio]
    exact hmonoW hiK
  · exact VSPAux.Bseq_anti _ hN _ _ hW0 hWle i K
  · have h1 : Bseq (Fintype.card L) (demandWorkload P) K 1 =
        (K : ℝ) / ((Fintype.card L : ℝ) + (K : ℝ) - 1 + demandWorkload P) := by
      rw [VSPAux.Bseq_succ, VSPAux.Bseq_zero, sub_zero, mul_one]
    rw [← h1]
    exact hmonoD hi
  · exact VSPAux.Bseq_strict _ hN _ hDpos i K hiK
