-- Prove2me | solution 1 for VehShare.MultiNet.static_pricing_multi_network_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T17:49:56.884693+00:00
-- url     : https://prove2.me/submissions/3d0bf729-b5fe-45d7-b444-6206fc177b08

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_ClosedNetwork
import Definitions.Def_VehShare_SeqBounds_Bseq
import Definitions.Def_VehShare_MultiNet_IsOptimal2
import Definitions.Def_VehShare_MultiNet_staticPolicy
import Definitions.Def_VehShare_MultiNet_IsStationary
import Definitions.Def_VehShare_MultiNet_ConcentratedOn
import Definitions.Def_VehShare_MultiNet_reward
import Definitions.Def_VehShare_MultiNet_Ropt
import Definitions.Def_VehShare_MultiNet_LamOverMu

set_option linter.unusedSimpArgs false

set_option autoImplicit false


namespace VehShare.MultiNet
/-- local copy of the strong-connectivity predicate (used for networks). -/
def FlowStronglyConnected (P : Instance) (qs : P.L → P.L → ℝ) : Prop :=
  ∀ i j : P.L, Relation.ReflTransGen (fun a b => 0 < P.Λ a b * qs a b) i j
end VehShare.MultiNet

namespace VSAux

open Finset VehicleSharePricing.Static VehShare.MultiNet
open VehShare.SeqBounds (Bseq)

/-- the infinite-server indicator on `L ⊕ T` -/
def isR {L T : Type*} (s : L ⊕ T) : Bool := s.isRight

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

variable {L : Type*} [Fintype L] [DecidableEq L] {T : Type*} [Fintype T] [DecidableEq T]

lemma busy_inl_eq (ρ : (L ⊕ T) → ℝ) (c : ℝ) (hin : ∀ i, ρ (Sum.inl i) = c) (K : ℕ) (i j : L) :
    pfBusyProb ρ isR K (Sum.inl i) = pfBusyProb ρ isR K (Sum.inl j) := by
  rcases K with _ | K
  · rw [busy_zero, busy_zero]
  · rw [busy_succ_single ρ isR K (Sum.inl i) rfl,
      busy_succ_single ρ isR K (Sum.inl j) rfl, hin, hin]

lemma busy_recursion [Nonempty L] (ρ : (L ⊕ T) → ℝ) (c W : ℝ) (hρ : ∀ s, 0 ≤ ρ s)
    (hc : 0 < c) (hin : ∀ i, ρ (Sum.inl i) = c)
    (hW : ∑ p : T, ρ (Sum.inr p) = c * W) (i : L) (K : ℕ) :
    pfBusyProb ρ isR (K + 1) (Sum.inl i) *
      ((Fintype.card L : ℝ) + K + W * (1 - pfBusyProb ρ isR K (Sum.inl i))) = K + 1 := by
  have hGpos : ∀ n, 0 < pfNormConst ρ isR n := fun n =>
    normConst_pos ρ isR hρ (Sum.inl i) rfl (by rw [hin]; exact hc) n
  have hISs : ∀ n (p : T), Lsum ρ isR (n + 1) (Sum.inr p) =
      ρ (Sum.inr p) * pfNormConst ρ isR n := fun n p =>
    Lsum_succ_IS ρ isR n (Sum.inr p) rfl
  have hSs : ∀ n (j : L), Lsum ρ isR (n + 1) (Sum.inl j) =
      c * (Lsum ρ isR n (Sum.inl j) + pfNormConst ρ isR n) := fun n j => by
    rw [Lsum_succ_single ρ isR n (Sum.inl j) rfl, hin]
  have hIS : ∀ n, ∑ p : T, Lsum ρ isR (n + 1) (Sum.inr p) =
      c * W * pfNormConst ρ isR n := by
    intro n
    simp only [hISs]
    rw [← Finset.sum_mul, hW]
  have hAeq : ∑ j : L, Lsum ρ isR K (Sum.inl j) = K * pfNormConst ρ isR K -
      W * pfBusyProb ρ isR K (Sum.inl i) * pfNormConst ρ isR K := by
    have htot := sum_Lsum ρ (isR (L := L) (T := T)) K
    rw [Fintype.sum_sum_type] at htot
    rcases K with _ | k
    · simp only [Lsum_zero, Finset.sum_const_zero, busy_zero]; simp
    · rw [hIS k] at htot
      rw [busy_succ_single ρ isR k (Sum.inl i) rfl, hin]
      have hne := (hGpos (k + 1)).ne'
      have e : W * (c * pfNormConst ρ isR k / pfNormConst ρ isR (k + 1)) *
          pfNormConst ρ isR (k + 1) = c * W * pfNormConst ρ isR k := by
        rw [mul_assoc, div_mul_cancel₀ _ hne]; ring
      rw [e]
      linarith
  have hkey : ((K : ℝ) + 1) * pfNormConst ρ isR (K + 1) =
      c * pfNormConst ρ isR K *
        ((Fintype.card L : ℝ) + K + W * (1 - pfBusyProb ρ isR K (Sum.inl i))) := by
    have htot := sum_Lsum ρ (isR (L := L) (T := T)) (K + 1)
    rw [Fintype.sum_sum_type, hIS K] at htot
    simp only [hSs] at htot
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hAeq] at htot
    push_cast at htot
    linarith
  rw [busy_succ_single ρ isR K (Sum.inl i) rfl, hin]
  have := hGpos (K + 1)
  rw [div_mul_eq_mul_div, div_eq_iff this.ne']
  linarith

lemma busy_eq_Bseq [Nonempty L] (ρ : (L ⊕ T) → ℝ) (c W : ℝ) (hρ : ∀ s, 0 ≤ ρ s)
    (hc : 0 < c) (hin : ∀ i, ρ (Sum.inl i) = c) (hW0 : 0 ≤ W)
    (hW : ∑ p : T, ρ (Sum.inr p) = c * W) (i : L) :
    ∀ K, pfBusyProb ρ isR K (Sum.inl i) = Bseq (Fintype.card L) W K K := by
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



end VSAux

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace VSPh

open Finset Matrix VehShare.MultiNet
open VehShare.SeqBounds (Bseq)

variable (P : Instance) (i j : P.L)

lemma negT_mulVec (x : P.Ph i j → ℝ) (a : P.Ph i j) :
    ((-subGen P i j) *ᵥ x) a =
      P.e i j a * x a + ∑ b ∈ univ.erase a, P.r i j a b * (x a - x b) := by
  have key : ∀ b ∈ univ.erase a, (-subGen P i j) a b * x b = -(P.r i j a b * x b) := by
    intro b hb
    simp [subGen, (Finset.ne_of_mem_erase hb).symm]
  have hdiag : (-subGen P i j) a a = P.e i j a + ∑ b ∈ univ.erase a, P.r i j a b := by
    simp [subGen]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), Finset.sum_congr rfl key, hdiag]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

lemma nonneg_of_negT (x : P.Ph i j → ℝ) (h : ∀ a, 0 ≤ ((-subGen P i j) *ᵥ x) a) :
    ∀ a, 0 ≤ x a := by
  by_contra hc
  push Not at hc
  obtain ⟨a0, ha0⟩ := hc
  obtain ⟨s0, -, hs0⟩ := Finset.exists_min_image univ x ⟨a0, mem_univ _⟩
  have hm : x s0 < 0 := lt_of_le_of_lt (hs0 a0 (mem_univ _)) ha0
  have step : ∀ a, x a = x s0 →
      P.e i j a = 0 ∧ ∀ b, a ≠ b → 0 < P.r i j a b → x b = x s0 := by
    intro a ha
    have h1 := h a
    rw [negT_mulVec] at h1
    have hterm : ∀ b ∈ univ.erase a, P.r i j a b * (x a - x b) ≤ 0 := fun b _ =>
      mul_nonpos_of_nonneg_of_nonpos (P.r_nonneg i j a b)
        (by rw [ha]; linarith [hs0 b (mem_univ _)])
    have he : P.e i j a * x a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (P.e_nonneg i j a) (by rw [ha]; exact hm.le)
    have hsum := Finset.sum_nonpos hterm
    have hsum0 : ∑ b ∈ univ.erase a, P.r i j a b * (x a - x b) = 0 := by linarith
    have he0 : P.e i j a * x a = 0 := by linarith
    refine ⟨?_, fun b hab hr => ?_⟩
    · rcases mul_eq_zero.1 he0 with h2 | h2
      · exact h2
      · rw [ha] at h2; linarith
    · have h3 := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 hsum0 b
        (mem_erase.2 ⟨hab.symm, mem_univ _⟩)
      rcases mul_eq_zero.1 h3 with h2 | h2
      · linarith
      · linarith
  obtain ⟨s', hpath, he⟩ := P.absorbing i j s0
  have hx : x s' = x s0 := by
    clear he
    induction hpath with
    | refl => rfl
    | tail _ hbc ih => exact (step _ ih).2 _ hbc.1 hbc.2
  exact absurd (step s' hx).1 (ne_of_gt he)

lemma eq_zero_of_negT (x : P.Ph i j → ℝ) (h : (-subGen P i j) *ᵥ x = 0) : x = 0 := by
  have h1 := nonneg_of_negT P i j x (fun a => by rw [h]; simp)
  have h2 := nonneg_of_negT P i j (-x) (fun a => by rw [Matrix.mulVec_neg, h]; simp)
  funext a
  have := h2 a
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  linarith [h1 a]

lemma negT_isUnit : IsUnit (-subGen P i j).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hv0⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  exact hv (eq_zero_of_negT P i j v hv0)

lemma inv_mulVec_nonneg (v : P.Ph i j → ℝ) (hv : ∀ a, 0 ≤ v a) :
    ∀ a, 0 ≤ ((-subGen P i j)⁻¹ *ᵥ v) a := by
  apply nonneg_of_negT
  intro a
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (negT_isUnit P i j), Matrix.one_mulVec]
  exact hv a

lemma inv_nonneg (a b : P.Ph i j) : 0 ≤ (-subGen P i j)⁻¹ a b := by
  have h := inv_mulVec_nonneg P i j (Pi.single b 1)
    (fun c => by by_cases hc : c = b <;> simp [Pi.single_apply, hc]) a
  simpa [Matrix.mulVec_single_one] using h

lemma meanTime_nonneg : 0 ≤ meanTime P i j := by
  unfold meanTime
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (P.β_nonneg i j a) (inv_mulVec_nonneg P i j _ (fun _ => zero_le_one) a)

/-- the stage loads of a pair with entry flow `c` -/
noncomputable def load (c : ℝ) : P.Ph i j → ℝ := c • Matrix.vecMul (P.β i j) (-subGen P i j)⁻¹

lemma load_nonneg (c : ℝ) (hc : 0 ≤ c) (s : P.Ph i j) : 0 ≤ load P i j c s := by
  unfold load
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct]
  exact mul_nonneg hc (Finset.sum_nonneg fun a _ =>
    mul_nonneg (P.β_nonneg i j a) (inv_nonneg P i j a s))

lemma load_balance (c : ℝ) : Matrix.vecMul (load P i j c) (-subGen P i j) = c • P.β i j := by
  unfold load
  rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (negT_isUnit P i j),
    Matrix.vecMul_one]

/-- any stage vector balanced by entry flow `c` has total `c * meanTime` -/
lemma sum_of_balance (m : P.Ph i j → ℝ) (c : ℝ) (hm : Matrix.vecMul m (-subGen P i j) = c • P.β i j) :
    ∑ s, m s = c * meanTime P i j := by
  have h1 : ∑ s, m s = m ⬝ᵥ ((-subGen P i j) *ᵥ ((-subGen P i j)⁻¹ *ᵥ fun _ => (1 : ℝ))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (negT_isUnit P i j), Matrix.one_mulVec]
    simp [dotProduct]
  rw [h1, Matrix.dotProduct_mulVec, hm, meanTime, smul_dotProduct, smul_eq_mul]

lemma load_sum (c : ℝ) : ∑ s, load P i j c s = c * meanTime P i j :=
  sum_of_balance P i j _ c (load_balance P i j c)

end VSPh

namespace VSProp1

open Finset Matrix VehShare.MultiNet
open VehShare.SeqBounds (Bseq)

variable {P : Instance} {K : ℕ}

/-- linear test function `z ↦ ∑ₓ w x z x` -/
noncomputable def linF (w : Slot P → ℝ) (z : State P K) : ℝ := ∑ x, w x * (z.1 x : ℝ)

lemma linF_move (w : Slot P → ℝ) (z : State P K) (a b : Slot P) (h : 1 ≤ z.1 a) :
    linF w (move z a b) - linF w z = w b - w a := by
  unfold linF move
  rw [dif_pos h]
  have hc : ∀ x, ((z.1 x - (if x = a then 1 else 0) + (if x = b then 1 else 0) : ℕ) : ℝ)
      = (z.1 x : ℝ) - (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
    intro x
    have hle : (if x = a then 1 else 0) ≤ z.1 x := by
      split_ifs with hxa
      · subst hxa; exact h
      · exact Nat.zero_le _
    rw [Nat.cast_add, Nat.cast_sub hle]
    split_ifs <;> simp
  simp only [hc, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, mem_univ, if_true]
  ring

lemma coef_move (w : Slot P → ℝ) (z : State P K) (a b : Slot P) (c d : ℝ)
    (hc : z.1 a = 0 → c = 0) :
    c * (d * (linF w (move z a b) - linF w z)) = c * (d * (w b - w a)) := by
  by_cases h : 1 ≤ z.1 a
  · rw [linF_move w z a b h]
  · rw [hc (by omega)]; simp

lemma sum_ne_erase {α : Type*} [Fintype α] [DecidableEq α] (s : α) (g : α → ℝ) :
    (∑ s', if s = s' then 0 else g s') = ∑ s' ∈ univ.erase s, g s' := by
  rw [← Finset.add_sum_erase _ _ (mem_univ s), if_pos rfl, zero_add]
  exact sum_congr rfl fun s' hs' => if_neg (Finset.ne_of_mem_erase hs').symm

lemma gen_linF (q : Policy P K) (w : Slot P → ℝ) (z : State P K) :
    gen q.1 (linF w) z =
      (∑ i, ∑ j, P.Λ i j * q.1 z i j *
        ((1 - ∑ s, P.β i j s) * (w (Sum.inl j) - w (Sum.inl i))
          + ∑ s, P.β i j s * (w (Sum.inr ⟨(i, j), s⟩) - w (Sum.inl i))))
      + (∑ i, ∑ j, ∑ s, ∑ s', if s = s' then 0 else
          (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
            (w (Sum.inr ⟨(i, j), s'⟩) - w (Sum.inr ⟨(i, j), s⟩)))
      + ∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
          (w (Sum.inl j) - w (Sum.inr ⟨(i, j), s⟩)) := by
  unfold gen
  congr 1
  congr 1
  · refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have hq : z.1 (Sum.inl i) = 0 → P.Λ i j * q.1 z i j = 0 := fun h => by
      rw [q.2.2 z i j h, mul_zero]
    rw [mul_add, mul_add, coef_move w z _ _ _ _ hq, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact sum_congr rfl fun s _ => coef_move w z _ _ _ _ hq
  · refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun s _ =>
      sum_congr rfl fun s' _ => ?_
    split_ifs
    · rfl
    · rw [mul_assoc, mul_assoc]
      exact coef_move w z _ _ _ _ (fun h => by simp [h])
  · refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun s _ => ?_
    have := coef_move w z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j)
      (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) (P.e i j s) (fun h => by simp [h])
    linarith [this]

/-- expected acceptance -/
noncomputable def qbar (q : Policy P K) (π : State P K → ℝ) (i j : P.L) : ℝ :=
  ∑ z, π z * q.1 z i j

lemma qbar_mem (q : Policy P K) (π : State P K → ℝ) (hπ : IsStationary q π) (i j : P.L) :
    0 ≤ qbar q π i j ∧ qbar q π i j ≤ 1 := by
  refine ⟨sum_nonneg fun z _ => mul_nonneg (hπ.1 z) (q.2.1 z i j).1, ?_⟩
  calc qbar q π i j ≤ ∑ z, π z * 1 :=
        sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (q.2.1 z i j).2 (hπ.1 z)
    _ = 1 := by simp [hπ.2.1]

lemma flow_balance (q : Policy P K) (π : State P K → ℝ) (hπ : IsStationary q π) (i0 : P.L) :
    ∑ j, P.Λ i0 j * qbar q π i0 j = ∑ j, P.Λ j i0 * qbar q π j i0 := by
  set w : Slot P → ℝ := Sum.elim (fun x => if x = i0 then 1 else 0)
    (fun σ => if σ.1.2 = i0 then 1 else 0) with hw
  have hgen : ∀ z, gen q.1 (linF w) z =
      ∑ i, ∑ j, P.Λ i j * q.1 z i j * ((if j = i0 then 1 else 0) - (if i = i0 then 1 else 0)) := by
    intro z
    rw [gen_linF]
    have h2 : (∑ i, ∑ j, ∑ s, ∑ s', if s = s' then (0:ℝ) else
          (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
            (w (Sum.inr ⟨(i, j), s'⟩) - w (Sum.inr ⟨(i, j), s⟩))) = 0 := by
      refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => sum_eq_zero fun s _ =>
        sum_eq_zero fun s' _ => ?_
      simp [hw]
    have h3 : (∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
          (w (Sum.inl j) - w (Sum.inr ⟨(i, j), s⟩))) = 0 := by
      refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => sum_eq_zero fun s _ => ?_
      simp [hw]
    rw [h2, h3, add_zero, add_zero]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have hs : ∀ x : P.Ph i j, P.β i j x * (w (Sum.inr ⟨(i, j), x⟩) - w (Sum.inl i)) =
        P.β i j x * (w (Sum.inl j) - w (Sum.inl i)) := fun x => by simp [hw]
    rw [Finset.sum_congr rfl (fun x _ => hs x), ← Finset.sum_mul]
    simp only [hw, Sum.elim_inl]
    ring
  have key : ∑ z, π z * gen q.1 (linF w) z = ∑ i, ∑ j, P.Λ i j * qbar q π i j *
      ((if j = i0 then (1:ℝ) else 0) - (if i = i0 then 1 else 0)) := by
    simp only [hgen, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold qbar
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by ring
  have h0 := hπ.2.2 (linF w)
  rw [key] at h0
  simp only [mul_sub, Finset.sum_sub_distrib] at h0
  have eA : ∀ X : P.L → P.L → ℝ, ∑ i, ∑ j, X i j * (if j = i0 then 1 else 0) = ∑ i, X i i0 :=
    fun X => by simp
  have eB : ∀ X : P.L → P.L → ℝ, ∑ i, ∑ j, X i j * (if i = i0 then 1 else 0) = ∑ j, X i0 j :=
    fun X => by
      rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hb]) (by simp)]
      simp
  have hA := eA (fun i j => P.Λ i j * qbar q π i j)
  have hB := eB (fun i j => P.Λ i j * qbar q π i j)
  linarith

/-- the expected number of vehicles in transit is `∑ Λ qbar meanTime` -/
lemma workload_qbar (q : Policy P K) (π : State P K → ℝ) (hπ : IsStationary q π) :
    workload P (qbar q π) = ∑ z, π z * ∑ σ : (Σ p : P.L × P.L, P.Ph p.1 p.2), (z.1 (Sum.inr σ) : ℝ) := by
  set h : ∀ p : P.L × P.L, P.Ph p.1 p.2 → ℝ :=
    fun p => (-subGen P p.1 p.2)⁻¹ *ᵥ (fun _ => (1 : ℝ)) with hh
  have hT : ∀ i j (s : P.Ph i j), P.e i j s * h (i, j) s +
      ∑ b ∈ univ.erase s, P.r i j s b * (h (i, j) s - h (i, j) b) = 1 := by
    intro i j s
    have := VSPh.negT_mulVec P i j (h (i, j)) s
    rw [← this, hh]
    simp only
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (VSPh.negT_isUnit P i j), Matrix.one_mulVec]
  set w : Slot P → ℝ := Sum.elim (fun _ => 0) (fun σ => h σ.1 σ.2) with hw
  have hgen : ∀ z : State P K, gen q.1 (linF w) z =
      ∑ i, ∑ j, P.Λ i j * q.1 z i j * meanTime P i j -
        ∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) := by
    intro z
    rw [gen_linF]
    have h1 : ∀ i j, (1 - ∑ s, P.β i j s) * (w (Sum.inl j) - w (Sum.inl i))
          + ∑ s, P.β i j s * (w (Sum.inr ⟨(i, j), s⟩) - w (Sum.inl i)) = meanTime P i j := by
      intro i j
      simp only [hw, Sum.elim_inl, Sum.elim_inr, sub_zero, sub_self, mul_zero, zero_add]
      rfl
    simp only [h1]
    have h23 : ∀ i j, (∑ s, ∑ s', if s = s' then (0:ℝ) else
          (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
            (w (Sum.inr ⟨(i, j), s'⟩) - w (Sum.inr ⟨(i, j), s⟩)))
        + ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
          (w (Sum.inl j) - w (Sum.inr ⟨(i, j), s⟩)) = -∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) := by
      intro i j
      rw [← sum_add_distrib, ← sum_neg_distrib]
      refine sum_congr rfl fun s _ => ?_
      rw [sum_ne_erase s]
      simp only [hw, Sum.elim_inl, Sum.elim_inr]
      have := hT i j s
      have e1 : ∑ x ∈ univ.erase s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s x *
          (h (i, j) x - h (i, j) s) = -((z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) *
            ∑ b ∈ univ.erase s, P.r i j s b * (h (i, j) s - h (i, j) b)) := by
        rw [Finset.mul_sum, ← sum_neg_distrib]
        exact sum_congr rfl fun x _ => by ring
      rw [e1]
      have e2 : (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * (∑ b ∈ univ.erase s, P.r i j s b *
          (h (i, j) s - h (i, j) b)) = (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) *
            (1 - P.e i j s * h (i, j) s) := by rw [← this]; ring
      rw [e2]
      ring
    have hsplit : (∑ i, ∑ j, ∑ s, ∑ s', if s = s' then (0:ℝ) else
          (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
            (w (Sum.inr ⟨(i, j), s'⟩) - w (Sum.inr ⟨(i, j), s⟩)))
        + (∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
          (w (Sum.inl j) - w (Sum.inr ⟨(i, j), s⟩))) =
          -∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) := by
      rw [← sum_add_distrib, ← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib, ← sum_neg_distrib]
      exact sum_congr rfl fun j _ => h23 i j
    rw [add_assoc, hsplit]
    ring
  have h0 := hπ.2.2 (linF w)
  simp only [hgen, mul_sub, sum_sub_distrib] at h0
  have hst : ∀ z : State P K, ∑ σ : (Σ p : P.L × P.L, P.Ph p.1 p.2), (z.1 (Sum.inr σ) : ℝ) =
      ∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) := by
    intro z
    rw [Fintype.sum_sigma, Fintype.sum_prod_type]
  simp only [hst]
  have hw' : workload P (qbar q π) = ∑ z, π z * ∑ i, ∑ j, P.Λ i j * q.1 z i j * meanTime P i j := by
    unfold workload qbar
    symm
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun z _ => by ring
  linarith

lemma transit_le (z : State P K) :
    ∑ σ : (Σ p : P.L × P.L, P.Ph p.1 p.2), (z.1 (Sum.inr σ) : ℝ) ≤ K := by
  have h := z.2
  rw [Fintype.sum_sum_type] at h
  have : (∑ σ : (Σ p : P.L × P.L, P.Ph p.1 p.2), z.1 (Sum.inr σ)) ≤ K := by omega
  exact_mod_cast this

theorem prop1 (Δ : ℝ) (hΔ : (K : ℝ) ≤ Δ) (qs : P.L → P.L → ℝ) (hqs : IsOptimal2 P Δ qs)
    (q : Policy P K) (π : State P K → ℝ) (hπ : IsStationary q π) : reward q π ≤ Rs P qs := by
  have hfeas : IsFeasible2 P Δ (qbar q π) := by
    refine ⟨qbar_mem q π hπ, flow_balance q π hπ, ?_⟩
    rw [workload_qbar q π hπ]
    calc ∑ z, π z * ∑ σ : (Σ p : P.L × P.L, P.Ph p.1 p.2), (z.1 (Sum.inr σ) : ℝ)
        ≤ ∑ z, π z * (K : ℝ) := sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (transit_le z) (hπ.1 z)
      _ = K := by rw [← Finset.sum_mul, hπ.2.1, one_mul]
      _ ≤ Δ := hΔ
  refine le_trans ?_ (hqs.2 _ hfeas)
  unfold reward Rs
  simp only [Finset.mul_sum]
  rw [sum_comm]
  refine sum_le_sum fun i _ => ?_
  rw [sum_comm]
  refine sum_le_sum fun j _ => ?_
  have hJ := (P.concave i j).le_map_sum (t := univ) (w := π) (p := fun z => q.1 z i j)
    (fun z _ => hπ.1 z) hπ.2.1 (fun z _ => ⟨(q.2.1 z i j).1, (q.2.1 z i j).2⟩)
  simp only [smul_eq_mul] at hJ
  calc ∑ z, π z * (P.Λ i j * q.1 z i j * P.I i j (q.1 z i j))
      = P.Λ i j * ∑ z, π z * (q.1 z i j * P.I i j (q.1 z i j)) := by
        rw [Finset.mul_sum]; exact sum_congr rfl fun z _ => by ring
    _ ≤ P.Λ i j * (qbar q π i j * P.I i j (qbar q π i j)) :=
        mul_le_mul_of_nonneg_left hJ (P.Λ_nonneg i j)
    _ = P.Λ i j * qbar q π i j * P.I i j (qbar q π i j) := by ring

end VSProp1

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace VSFlux

open Finset VehShare.MultiNet
open VehShare.SeqBounds (Bseq)

variable {P : Instance} {K : ℕ}

/-- one transition of positive rate of the chain under `q` -/
abbrev Step (q : Policy P K) (z w : State P K) : Prop :=
  (∃ i j, 0 < P.Λ i j * q.1 z i j * (1 - ∑ s, P.β i j s) ∧ w = move z (Sum.inl i) (Sum.inl j)) ∨
  (∃ i j, ∃ s : P.Ph i j, 0 < P.Λ i j * q.1 z i j * P.β i j s ∧
      w = move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)) ∨
  (∃ i j, ∃ s s' : P.Ph i j, s ≠ s' ∧ 0 < (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' ∧
      w = move z (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩)) ∨
  (∃ i j, ∃ s : P.Ph i j, 0 < (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s ∧
      w = move z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j))

lemma one_sub_beta (i j : P.L) : 0 ≤ 1 - ∑ s, P.β i j s := by
  linarith [P.β_sum_le i j]

lemma gen_at_zero (q : Policy P K) (f : State P K → ℝ) (z : State P K) (hz : f z = 0) :
    gen q.1 f z =
      (∑ i, ∑ j, P.Λ i j * q.1 z i j *
        ((1 - ∑ s, P.β i j s) * f (move z (Sum.inl i) (Sum.inl j))
          + ∑ s, P.β i j s * f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩))))
      + (∑ i, ∑ j, ∑ s, ∑ s', if s = s' then 0 else
          (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
            f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩)))
      + ∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
          f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j)) := by
  unfold gen
  rw [hz]
  simp only [sub_zero]


lemma pA_nonneg (q : Policy P K) (f : State P K → ℝ) (hf : ∀ x, 0 ≤ f x) (z : State P K) (i j : P.L) : 0 ≤ P.Λ i j * q.1 z i j *
    ((1 - ∑ s, P.β i j s) * f (move z (Sum.inl i) (Sum.inl j))
      + ∑ s, P.β i j s * f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩))) :=
  mul_nonneg (mul_nonneg (P.Λ_nonneg i j) (q.2.1 z i j).1)
    (add_nonneg (mul_nonneg (one_sub_beta i j) (hf _))
      (sum_nonneg fun s _ => mul_nonneg (P.β_nonneg i j s) (hf _)))

lemma pB_nonneg (f : State P K → ℝ) (hf : ∀ x, 0 ≤ f x) (z : State P K) (i j : P.L) (s s' : P.Ph i j) : 0 ≤ (if s = s' then 0 else
    (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
      f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩))) := by
  split_ifs
  · exact le_refl 0
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (P.r_nonneg i j s s')) (hf _)

lemma pC_nonneg (f : State P K → ℝ) (hf : ∀ x, 0 ≤ f x) (z : State P K) (i j : P.L) (s : P.Ph i j) : 0 ≤ (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
    f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j)) :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (P.e_nonneg i j s)) (hf _)

lemma sA_nonneg (q : Policy P K) (f : State P K → ℝ) (hf : ∀ x, 0 ≤ f x) (z : State P K) : 0 ≤ ∑ i, ∑ j, P.Λ i j * q.1 z i j *
    ((1 - ∑ s, P.β i j s) * f (move z (Sum.inl i) (Sum.inl j))
      + ∑ s, P.β i j s * f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩))) :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => pA_nonneg q f hf z i j

lemma sB_nonneg (f : State P K → ℝ) (hf : ∀ x, 0 ≤ f x) (z : State P K) : 0 ≤ ∑ i, ∑ j, ∑ s, ∑ s', if s = s' then 0 else
    (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
      f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩)) :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun s _ => sum_nonneg fun s' _ =>
    pB_nonneg f hf z i j s s'

lemma sC_nonneg (f : State P K → ℝ) (hf : ∀ x, 0 ≤ f x) (z : State P K) : 0 ≤ ∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
    f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j)) :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun s _ => pC_nonneg f hf z i j s

lemma gen_nonneg_of_zero (q : Policy P K) (f : State P K → ℝ) (hf : ∀ x, 0 ≤ f x) (z : State P K) (hz : f z = 0) : 0 ≤ gen q.1 f z := by
  rw [gen_at_zero q f z hz]
  exact add_nonneg (add_nonneg (sA_nonneg q f hf z) (sB_nonneg f hf z)) (sC_nonneg f hf z)

/-- a successor of a zero of a nonnegative `f` with `gen f z ≤ 0` is a zero -/
lemma step_zero (q : Policy P K) (f : State P K → ℝ) (hf : ∀ x, 0 ≤ f x) (z : State P K) (hz : f z = 0) (hg : gen q.1 f z ≤ 0) (w : State P K) (hs : Step q z w) :
    f w = 0 := by
  rw [gen_at_zero q f z hz] at hg
  have hA := sA_nonneg q f hf z
  have hB := sB_nonneg f hf z
  have hC := sC_nonneg f hf z
  have eA : (∑ i, ∑ j, P.Λ i j * q.1 z i j *
      ((1 - ∑ s, P.β i j s) * f (move z (Sum.inl i) (Sum.inl j))
        + ∑ s, P.β i j s * f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)))) ≤ 0 := by linarith
  have eB : (∑ i, ∑ j, ∑ s, ∑ s', if s = s' then (0:ℝ) else
      (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
        f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩))) ≤ 0 := by linarith
  have eC : (∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
      f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j))) ≤ 0 := by linarith
  -- each summand is bounded by its sum
  have tA : ∀ i j, P.Λ i j * q.1 z i j *
      ((1 - ∑ s, P.β i j s) * f (move z (Sum.inl i) (Sum.inl j))
        + ∑ s, P.β i j s * f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩))) ≤ 0 := fun i j =>
    le_trans ((single_le_sum (fun j _ => pA_nonneg q f hf z i j) (mem_univ j)).trans
      (single_le_sum (f := fun i => ∑ j, P.Λ i j * q.1 z i j *
      ((1 - ∑ s, P.β i j s) * f (move z (Sum.inl i) (Sum.inl j))
        + ∑ s, P.β i j s * f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩))))
        (fun i _ => sum_nonneg fun j _ => pA_nonneg q f hf z i j) (mem_univ i))) eA
  have tB : ∀ i j (s s' : P.Ph i j), (if s = s' then (0:ℝ) else
      (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
        f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩))) ≤ 0 := fun i j s s' => by
    refine le_trans ?_ eB
    refine le_trans ?_ (single_le_sum (f := fun i => ∑ j, ∑ s, ∑ s', if s = s' then (0:ℝ) else
      (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
        f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩)))
      (fun i _ => sum_nonneg fun j _ => sum_nonneg fun s _ => sum_nonneg fun s' _ =>
        pB_nonneg f hf z i j s s') (mem_univ i))
    refine le_trans ?_ (single_le_sum (fun j _ => sum_nonneg fun s _ => sum_nonneg fun s' _ =>
        pB_nonneg f hf z i j s s') (mem_univ j))
    refine le_trans ?_ (single_le_sum (fun s _ => sum_nonneg fun s' _ =>
        pB_nonneg f hf z i j s s') (mem_univ s))
    exact single_le_sum (fun s' _ => pB_nonneg f hf z i j s s') (mem_univ s')
  have tC : ∀ i j (s : P.Ph i j), (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
      f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j)) ≤ 0 := fun i j s => by
    refine le_trans ?_ eC
    refine le_trans ?_ (single_le_sum (f := fun i => ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) *
      P.e i j s * f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j)))
      (fun i _ => sum_nonneg fun j _ => sum_nonneg fun s _ => pC_nonneg f hf z i j s) (mem_univ i))
    refine le_trans ?_ (single_le_sum (fun j _ => sum_nonneg fun s _ =>
        pC_nonneg f hf z i j s) (mem_univ j))
    exact single_le_sum (fun s _ => pC_nonneg f hf z i j s) (mem_univ s)
  rcases hs with ⟨i, j, hpos, rfl⟩ | ⟨i, j, s, hpos, rfl⟩ | ⟨i, j, s, s', hne, hpos, rfl⟩ |
      ⟨i, j, s, hpos, rfl⟩
  · have h1 := tA i j
    have h2 : 0 ≤ P.Λ i j * q.1 z i j * ∑ s, P.β i j s *
        f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)) :=
      mul_nonneg (mul_nonneg (P.Λ_nonneg i j) (q.2.1 z i j).1)
        (sum_nonneg fun s _ => mul_nonneg (P.β_nonneg i j s) (hf _))
    have h3 : P.Λ i j * q.1 z i j * (1 - ∑ s, P.β i j s) *
        f (move z (Sum.inl i) (Sum.inl j)) ≤ 0 := by nlinarith
    exact le_antisymm (nonpos_of_mul_nonpos_right h3 hpos |> fun h => by linarith [hf (move z (Sum.inl i) (Sum.inl j))]) (hf _)
  · have h1 := tA i j
    have hs0 : P.β i j s * f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)) ≤
        ∑ s, P.β i j s * f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)) :=
      single_le_sum (f := fun s => P.β i j s * f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)))
        (fun s _ => mul_nonneg (P.β_nonneg i j s) (hf _)) (mem_univ s)
    have hc : 0 ≤ P.Λ i j * q.1 z i j := mul_nonneg (P.Λ_nonneg i j) (q.2.1 z i j).1
    have h0 : 0 ≤ (1 - ∑ s, P.β i j s) * f (move z (Sum.inl i) (Sum.inl j)) :=
      mul_nonneg (one_sub_beta i j) (hf _)
    have h3 : P.Λ i j * q.1 z i j * P.β i j s *
        f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)) ≤ 0 := by
      have := mul_le_mul_of_nonneg_left hs0 hc
      nlinarith
    exact le_antisymm (by
      have := nonpos_of_mul_nonpos_right h3 hpos
      linarith) (hf _)
  · have h1 := tB i j s s'
    rw [if_neg hne] at h1
    exact le_antisymm (by have := nonpos_of_mul_nonpos_right h1 hpos; linarith) (hf _)
  · have h1 := tC i j s
    exact le_antisymm (by have := nonpos_of_mul_nonpos_right h1 hpos; linarith) (hf _)


lemma zero_of (c d : ℝ) (hc : 0 ≤ c) (h : 0 < c → d = 0) : c * d = 0 := by
  rcases hc.eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]
  · rw [h h0, mul_zero]

/-- `gen f z = 0` when `f` is constant on the successors of `z` -/
lemma gen_zero_of_const (q : Policy P K) (f : State P K → ℝ) (z : State P K)
    (h : ∀ w, Step q z w → f w = f z) : gen q.1 f z = 0 := by
  unfold gen
  have hA : ∀ i j, P.Λ i j * q.1 z i j *
      ((1 - ∑ s, P.β i j s) * (f (move z (Sum.inl i) (Sum.inl j)) - f z)
        + ∑ s, P.β i j s * (f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)) - f z)) = 0 := by
    intro i j
    rw [mul_add, Finset.mul_sum]
    have hc : 0 ≤ P.Λ i j * q.1 z i j := mul_nonneg (P.Λ_nonneg i j) (q.2.1 z i j).1
    have e1 : P.Λ i j * q.1 z i j * ((1 - ∑ s, P.β i j s) *
        (f (move z (Sum.inl i) (Sum.inl j)) - f z)) = 0 := by
      rw [← mul_assoc]
      exact zero_of _ _ (mul_nonneg hc (one_sub_beta i j)) fun hp =>
        sub_eq_zero.mpr (h _ (Or.inl ⟨i, j, hp, rfl⟩))
    have e2 : ∀ s, P.Λ i j * q.1 z i j * (P.β i j s *
        (f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)) - f z)) = 0 := by
      intro s
      rw [← mul_assoc]
      exact zero_of _ _ (mul_nonneg hc (P.β_nonneg i j s)) fun hp =>
        sub_eq_zero.mpr (h _ (Or.inr (Or.inl ⟨i, j, s, hp, rfl⟩)))
    rw [e1, Finset.sum_eq_zero fun s _ => e2 s, add_zero]
  have hB : ∀ i j (s s' : P.Ph i j), (if s = s' then (0:ℝ) else
      (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
        (f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩)) - f z)) = 0 := by
    intro i j s s'
    split_ifs with hne
    · rfl
    · exact zero_of _ _ (mul_nonneg (Nat.cast_nonneg _) (P.r_nonneg i j s s')) fun hp =>
        sub_eq_zero.mpr (h _ (Or.inr (Or.inr (Or.inl ⟨i, j, s, s', hne, hp, rfl⟩))))
  have hC : ∀ i j (s : P.Ph i j), (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
      (f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j)) - f z) = 0 := by
    intro i j s
    exact zero_of _ _ (mul_nonneg (Nat.cast_nonneg _) (P.e_nonneg i j s)) fun hp =>
      sub_eq_zero.mpr (h _ (Or.inr (Or.inr (Or.inr ⟨i, j, s, hp, rfl⟩))))
  simp only [hA, hB, hC, Finset.sum_const_zero, add_zero]

/-- for a nonpositive signed invariant measure, the zero set is closed under predecessors -/
lemma pred_closed (q : Policy P K) (v : State P K → ℝ)
    (hv : ∀ f : State P K → ℝ, ∑ z, v z * gen q.1 f z = 0) (hle : ∀ z, v z ≤ 0)
    (z w : State P K) (hs : Step q z w) (hw : v w = 0) : v z = 0 := by
  by_contra hz
  have hzn : v z < 0 := lt_of_le_of_ne (hle z) hz
  set f : State P K → ℝ := fun x => if v x = 0 then 1 else 0 with hfdef
  have hf : ∀ x, 0 ≤ f x := fun x => by simp only [hfdef]; split_ifs <;> norm_num
  have hterm : ∀ x ∈ (univ : Finset (State P K)), v x * gen q.1 f x ≤ 0 := by
    intro x _
    by_cases hx : v x = 0
    · rw [hx, zero_mul]
    · have hfx : f x = 0 := by simp only [hfdef, if_neg hx]
      exact mul_nonpos_of_nonpos_of_nonneg (hle x) (gen_nonneg_of_zero q f hf x hfx)
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp (hv f) z (mem_univ z)
  have hfz : f z = 0 := by simp only [hfdef, if_neg hz]
  have hg : gen q.1 f z = 0 := by
    rcases mul_eq_zero.mp hall with h | h
    · exact absurd h hz
    · exact h
  have := step_zero q f hf z hfz hg.le w hs
  simp only [hfdef, if_pos hw] at this
  exact one_ne_zero this

/-- the support of a stationary law is closed under steps -/
lemma supp_closed (q : Policy P K) (π : State P K → ℝ) (hπ : IsStationary q π)
    (z w : State P K) (hs : Step q z w) (hz : 0 < π z) : 0 < π w := by
  rcases (hπ.1 w).eq_or_lt with h | h
  · exfalso
    have := pred_closed q (fun x => -π x)
      (fun f => by
        have := hπ.2.2 f
        simp only [neg_mul, Finset.sum_neg_distrib, this, neg_zero])
      (fun x => neg_nonpos.mpr (hπ.1 x)) z w hs (by simp [← h])
    simp at this
    linarith
  · exact h

end VSFlux
-- E_reach: body only; must follow D_flux (namespace VSFlux) in the concatenation.

namespace VSReach

open Finset VehShare.MultiNet VSFlux
open VehShare.SeqBounds (Bseq)

variable {P : Instance} {K : ℕ}

lemma move_val (z : State P K) (a b : Slot P) (h : 1 ≤ z.1 a) (x : Slot P) :
    (move z a b).1 x = z.1 x - (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
  unfold move
  rw [dif_pos h]

lemma move_self (z : State P K) (a : Slot P) : move z a a = z := by
  by_cases h : 1 ≤ z.1 a
  · apply Subtype.ext
    funext x
    rw [move_val z a a h]
    split_ifs with hx
    · subst hx; omega
    · simp
  · unfold move
    rw [dif_neg h]

lemma occ_move (z : State P K) (a b : Slot P) (h : 1 ≤ z.1 a) : 1 ≤ (move z a b).1 b := by
  rw [move_val z a b h]
  by_cases hba : b = a
  · subst hba
    rw [if_pos rfl]
    omega
  · rw [if_neg hba, if_pos rfl]
    omega

lemma move_move (z : State P K) (a b c : Slot P) (h : 1 ≤ z.1 a) :
    move (move z a b) b c = move z a c := by
  have hb := occ_move z a b h
  apply Subtype.ext
  funext x
  rw [move_val _ b c hb, move_val z a b h, move_val z a c h]
  split_ifs <;> subst_vars <;> omega

/-- a slot-level move that lifts to a positive-rate transition from every state occupying the source -/
def SlotStep (q : Policy P K) (a b : Slot P) : Prop :=
  ∀ z : State P K, 1 ≤ z.1 a → Step q z (move z a b)

lemma lift (q : Policy P K) {a t : Slot P} (hr : Relation.ReflTransGen (SlotStep q) a t)
    (z : State P K) (h : 1 ≤ z.1 a) : Relation.ReflTransGen (Step q) z (move z a t) := by
  induction hr with
  | refl => rw [move_self]
  | @tail b c _ hbc ih =>
    have hb := occ_move z a b h
    have hs := hbc _ hb
    rw [move_move z a b c h] at hs
    exact ih.tail hs

section static

variable (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1)

lemma static_q (z : State P K) (i j : P.L) (hz : 1 ≤ z.1 (Sum.inl i)) :
    (staticPolicy P K qs hqs).1 z i j = qs i j := by
  simp [staticPolicy, hz]

lemma ss_direct (i j : P.L) (h : 0 < P.Λ i j * qs i j * (1 - ∑ s, P.β i j s)) :
    SlotStep (staticPolicy P K qs hqs) (Sum.inl i) (Sum.inl j) := by
  intro z hz
  left
  exact ⟨i, j, by rw [static_q qs hqs z i j hz]; exact h, rfl⟩

lemma ss_in (i j : P.L) (s : P.Ph i j) (h : 0 < P.Λ i j * qs i j * P.β i j s) :
    SlotStep (staticPolicy P K qs hqs) (Sum.inl i) (Sum.inr ⟨(i, j), s⟩) := by
  intro z hz
  right; left
  exact ⟨i, j, s, by rw [static_q qs hqs z i j hz]; exact h, rfl⟩

lemma ss_move (i j : P.L) (s s' : P.Ph i j) (hne : s ≠ s') (h : 0 < P.r i j s s') :
    SlotStep (staticPolicy P K qs hqs) (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩) := by
  intro z hz
  right; right; left
  have hz' : (0 : ℝ) < (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) := Nat.cast_pos.mpr (by omega)
  exact ⟨i, j, s, s', hne, mul_pos hz' h, rfl⟩

lemma ss_drop (i j : P.L) (s : P.Ph i j) (h : 0 < P.e i j s) :
    SlotStep (staticPolicy P K qs hqs) (Sum.inr ⟨(i, j), s⟩) (Sum.inl j) := by
  intro z hz
  right; right; right
  have hz' : (0 : ℝ) < (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) := Nat.cast_pos.mpr (by omega)
  exact ⟨i, j, s, mul_pos hz' h, rfl⟩

lemma stage_reach (i j : P.L) (s : P.Ph i j) :
    Relation.ReflTransGen (SlotStep (staticPolicy P K qs hqs)) (Sum.inr ⟨(i, j), s⟩) (Sum.inl j) := by
  obtain ⟨s', hpath, he⟩ := P.absorbing i j s
  have h1 : Relation.ReflTransGen (SlotStep (staticPolicy P K qs hqs))
      (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩) :=
    Relation.ReflTransGen.lift (fun x => (Sum.inr ⟨(i, j), x⟩ : Slot P))
      (fun a b hab => ss_move qs hqs i j a b hab.1 hab.2) _ _ hpath
  exact h1.tail (ss_drop qs hqs i j s' he)

lemma edge_reach (a b : P.L) (h : 0 < P.Λ a b * qs a b) :
    Relation.ReflTransGen (SlotStep (staticPolicy P K qs hqs)) (Sum.inl a) (Sum.inl b) := by
  by_cases hd : 0 < 1 - ∑ s, P.β a b s
  · exact Relation.ReflTransGen.single (ss_direct qs hqs a b (mul_pos h hd))
  · have hex : ∃ s, 0 < P.β a b s := by
      by_contra hne
      push Not at hne
      have : ∑ s, P.β a b s ≤ 0 := Finset.sum_nonpos (fun s _ => hne s)
      linarith
    obtain ⟨s, hs⟩ := hex
    exact Relation.ReflTransGen.head (ss_in qs hqs a b s (mul_pos h hs)) (stage_reach qs hqs a b s)

lemma slot_reach (hsc : FlowStronglyConnected P qs) (i0 : P.L) (x : Slot P) :
    Relation.ReflTransGen (SlotStep (staticPolicy P K qs hqs)) x (Sum.inl i0) := by
  have loc : ∀ i, Relation.ReflTransGen (SlotStep (staticPolicy P K qs hqs)) (Sum.inl i) (Sum.inl i0) :=
    fun i => Relation.ReflTransGen.lift' (fun y => (Sum.inl y : Slot P))
      (fun a b hab => edge_reach qs hqs a b hab) _ _ (hsc i i0)
  rcases x with i | ⟨⟨i, j⟩, s⟩
  · exact loc i
  · exact (stage_reach qs hqs i j s).trans (loc j)

/-- the state with every vehicle parked at `i0` -/
def z0 (P : Instance) (K : ℕ) (i0 : P.L) : State P K :=
  ⟨fun x => if x = Sum.inl i0 then K else 0, by simp⟩

lemma reach_z0 (hsc : FlowStronglyConnected P qs) (i0 : P.L) (z : State P K) :
    Relation.ReflTransGen (Step (staticPolicy P K qs hqs)) z (z0 P K i0) := by
  suffices H : ∀ n : ℕ, ∀ z : State P K, K - z.1 (Sum.inl i0) = n →
      Relation.ReflTransGen (Step (staticPolicy P K qs hqs)) z (z0 P K i0) from H _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hn
    have hle : z.1 (Sum.inl i0) ≤ K :=
      (Finset.single_le_sum (f := z.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)).trans_eq z.2
    by_cases hfull : z.1 (Sum.inl i0) = K
    · have hz : z = z0 P K i0 := by
        apply Subtype.ext
        funext x
        show z.1 x = if x = Sum.inl i0 then K else 0
        split_ifs with hx
        · rw [hx, hfull]
        · have h2 : ∑ y ∈ ({x, Sum.inl i0} : Finset (Slot P)), z.1 y ≤ ∑ y, z.1 y :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          rw [Finset.sum_pair hx, z.2, hfull] at h2
          omega
      rw [hz]
    · have hex : ∃ a, a ≠ Sum.inl i0 ∧ 1 ≤ z.1 a := by
        by_contra hne
        push Not at hne
        have : ∑ y, z.1 y = z.1 (Sum.inl i0) :=
          Finset.sum_eq_single (Sum.inl i0) (fun b _ hb => by have := hne b hb; omega)
            (by simp)
        rw [z.2] at this
        exact hfull this.symm
      obtain ⟨a, ha, hza⟩ := hex
      have hR := lift _ (slot_reach qs hqs hsc i0 a) z hza
      have hv : (move z a (Sum.inl i0)).1 (Sum.inl i0) = z.1 (Sum.inl i0) + 1 := by
        rw [move_val z a _ hza]
        simp [Ne.symm ha]
      exact hR.trans (ih _ (by omega) _ rfl)

/-- a stationary law of the static chain lives on the states reachable from `z0` -/
lemma supp_reach (hsc : FlowStronglyConnected P qs) (i0 : P.L) (π : State P K → ℝ)
    (hπ : IsStationary (staticPolicy P K qs hqs) π) (z : State P K) (hz : 0 < π z) :
    Relation.ReflTransGen (Step (staticPolicy P K qs hqs)) (z0 P K i0) z := by
  classical
  set q := staticPolicy P K qs hqs
  set T : State P K → Prop := fun x => Relation.ReflTransGen (Step q) (z0 P K i0) x with hT
  set f : State P K → ℝ := fun x => if T x then 1 else 0 with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; split_ifs <;> norm_num
  have hterm : ∀ x ∈ (univ : Finset (State P K)), 0 ≤ π x * gen q.1 f x := by
    intro x _
    by_cases hx : T x
    · have : gen q.1 f x = 0 := gen_zero_of_const q f x (fun w hw => by
        have hw' : T w := Relation.ReflTransGen.tail hx hw
        simp only [hf, if_pos hw', if_pos hx])
      rw [this, mul_zero]
    · exact mul_nonneg (hπ.1 x) (gen_nonneg_of_zero q f hf0 x (by simp only [hf, if_neg hx]))
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp (hπ.2.2 f)
  -- from a positive state outside T, every successor stays outside T
  have key : ∀ x, 0 < π x → ¬ T x → ∀ w, Step q x w → ¬ T w := by
    intro x hx hxT w hs hwT
    have hg : gen q.1 f x = 0 := by
      rcases mul_eq_zero.mp (hall x (mem_univ x)) with h | h
      · linarith
      · exact h
    have := step_zero q f hf0 x (by simp only [hf, if_neg hxT]) hg.le w hs
    simp only [hf, if_pos hwT] at this
    exact one_ne_zero this
  by_contra hzT
  have hpath := reach_z0 qs hqs hsc i0 z
  have : ∀ y, Relation.ReflTransGen (Step q) z y → 0 < π y ∧ ¬ T y := by
    intro y hy
    induction hy with
    | refl => exact ⟨hz, hzT⟩
    | @tail b c _ hbc ih =>
      exact ⟨supp_closed q π hπ b c hbc ih.1, key b ih.1 ih.2 c hbc⟩
  exact (this _ hpath).2 Relation.ReflTransGen.refl

lemma back_zero (q : Policy P K) (v : State P K → ℝ)
    (hv : ∀ f : State P K → ℝ, ∑ z, v z * gen q.1 f z = 0) (hle : ∀ z, v z ≤ 0)
    {x y : State P K} (h : Relation.ReflTransGen (Step q) x y) (hy : v y = 0) : v x = 0 := by
  induction h with
  | refl => exact hy
  | @tail b c _ hbc ih => exact ih (pred_closed q v hv hle b c hbc hy)

/-- the static chain has at most one stationary law -/
theorem stat_unique [Nonempty P.L] (hsc : FlowStronglyConnected P qs) (π π' : State P K → ℝ)
    (hπ : IsStationary (staticPolicy P K qs hqs) π) (hπ' : IsStationary (staticPolicy P K qs hqs) π') :
    π = π' := by
  classical
  set q := staticPolicy P K qs hqs
  set i0 : P.L := Classical.arbitrary P.L
  set S := (univ : Finset (State P K)).filter (fun z => 0 < π' z) with hSdef
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h0 : ∀ z, π' z = 0 := fun z => by
      by_contra hz
      have hm : z ∈ S := Finset.mem_filter.mpr ⟨mem_univ z, lt_of_le_of_ne (hπ'.1 z) (Ne.symm hz)⟩
      rw [hne] at hm
      simp at hm
    have := hπ'.2.1
    simp [h0] at this
  obtain ⟨z1, hz1S, hmin⟩ := Finset.exists_min_image S (fun z => π z / π' z) hSne
  have hz1 : 0 < π' z1 := (Finset.mem_filter.mp hz1S).2
  set t := π z1 / π' z1 with htdef
  set v : State P K → ℝ := fun z => t * π' z - π z with hvdef
  have hle : ∀ z, v z ≤ 0 := by
    intro z
    simp only [hvdef]
    by_cases hz : 0 < π' z
    · have := hmin z (Finset.mem_filter.mpr ⟨mem_univ z, hz⟩)
      rw [le_div_iff₀ hz] at this
      linarith
    · have : π' z = 0 := le_antisymm (not_lt.mp hz) (hπ'.1 z)
      rw [this, mul_zero]
      linarith [hπ.1 z]
  have hv : ∀ f : State P K → ℝ, ∑ z, v z * gen q.1 f z = 0 := by
    intro f
    have e : ∀ z, v z * gen q.1 f z = t * (π' z * gen q.1 f z) - π z * gen q.1 f z := fun z => by
      simp only [hvdef]; ring
    rw [Finset.sum_congr rfl (fun z _ => e z), Finset.sum_sub_distrib, ← Finset.mul_sum,
      hπ.2.2 f, hπ'.2.2 f]
    ring
  have hvz1 : v z1 = 0 := by
    show t * π' z1 - π z1 = 0
    rw [htdef, div_mul_cancel₀ _ hz1.ne', sub_self]
  have hv0 : v (z0 P K i0) = 0 :=
    back_zero q v hv hle (supp_reach qs hqs hsc i0 π' hπ' z1 hz1) hvz1
  have hvall : ∀ z, v z = 0 := fun z => back_zero q v hv hle (reach_z0 qs hqs hsc i0 z) hv0
  have h1 : ∑ z, v z = t * ∑ z, π' z - ∑ z, π z := by
    simp only [hvdef]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hπ.2.1, hπ'.2.1, Finset.sum_eq_zero (fun z _ => hvall z)] at h1
  have ht : t = 1 := by linarith
  funext z
  have := hvall z
  simp only [hvdef, ht, one_mul] at this
  linarith

end static

end VSReach
-- F_pf: body only; must follow A_pf (VSAux) and B_ph (VSPh) in the concatenation.

namespace VSPF

open Finset Matrix VehicleSharePricing.Static VehShare.MultiNet VSAux VSPh
open VehShare.SeqBounds (Bseq)

variable {P : Instance}

lemma sum_ne_erase' {α : Type*} [Fintype α] [DecidableEq α] (s : α) (g : α → ℝ) :
    (∑ s', if s = s' then 0 else g s') = ∑ s' ∈ univ.erase s, g s' := by
  rw [← Finset.add_sum_erase _ _ (mem_univ s), if_pos rfl, zero_add]
  exact sum_congr rfl fun s' hs' => if_neg (Finset.ne_of_mem_erase hs').symm

/-- balance of the stage loads, tested against a stage function `x` -/
lemma key_id (i j : P.L) (m : P.Ph i j → ℝ) (c : ℝ)
    (hm : Matrix.vecMul m (-subGen P i j) = c • P.β i j) (x : P.Ph i j → ℝ) :
    ∑ s, m s * (P.e i j s * x s + ∑ b ∈ univ.erase s, P.r i j s b * (x s - x b)) =
      c * ∑ s, P.β i j s * x s := by
  have h := Matrix.dotProduct_mulVec m (-subGen P i j) x
  rw [hm] at h
  simp only [dotProduct, VSPh.negT_mulVec, Pi.smul_apply, smul_eq_mul] at h
  rw [h, Finset.mul_sum]
  exact sum_congr rfl fun s _ => by ring

lemma stage_ident (i j : P.L) (m : P.Ph i j → ℝ) (c : ℝ)
    (hm : Matrix.vecMul m (-subGen P i j) = c • P.β i j) (x : P.Ph i j → ℝ) (u : ℝ) :
    (∑ s, ∑ s', if s = s' then 0 else m s * P.r i j s s' * (x s' - x s)) +
      ∑ s, m s * P.e i j s * (u - x s) + c * ∑ s, P.β i j s * x s =
        c * (∑ s, P.β i j s) * u := by
  have k1 := key_id i j m c hm x
  have k2 := key_id i j m c hm (fun _ => 1)
  simp only [sub_self, mul_zero, Finset.sum_const_zero, add_zero, mul_one] at k2
  have p1 : ∀ s, (∑ s', if s = s' then 0 else m s * P.r i j s s' * (x s' - x s)) =
      -(m s * ∑ b ∈ univ.erase s, P.r i j s b * (x s - x b)) := by
    intro s
    rw [sum_ne_erase' s (fun s' => m s * P.r i j s s' * (x s' - x s)), Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [sum_congr rfl (fun s _ => p1 s)]
  have e1 : ∑ s, m s * P.e i j s * (u - x s) =
      u * ∑ s, m s * P.e i j s - ∑ s, m s * P.e i j s * x s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have e2 : ∑ s, m s * (P.e i j s * x s + ∑ b ∈ univ.erase s, P.r i j s b * (x s - x b)) =
      ∑ s, m s * P.e i j s * x s + ∑ s, m s * ∑ b ∈ univ.erase s, P.r i j s b * (x s - x b) := by
    rw [← Finset.sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [e1, Finset.sum_neg_distrib]
  rw [e2] at k1
  linear_combination (-1 : ℝ) * k1 + u * k2

/-- the three parts of the traffic expression -/
noncomputable def TA (qs : P.L → P.L → ℝ) (g : Slot P → ℝ) : ℝ :=
  ∑ i, ∑ j, P.Λ i j * qs i j *
    ((1 - ∑ s, P.β i j s) * (g (Sum.inl j) - g (Sum.inl i)) +
      ∑ s, P.β i j s * (g (Sum.inr ⟨(i, j), s⟩) - g (Sum.inl i)))

noncomputable def TB (qs : P.L → P.L → ℝ) (g : Slot P → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ s, ∑ s', if s = s' then 0 else
    load P i j (P.Λ i j * qs i j) s * P.r i j s s' *
      (g (Sum.inr ⟨(i, j), s'⟩) - g (Sum.inr ⟨(i, j), s⟩))

noncomputable def TC (qs : P.L → P.L → ℝ) (g : Slot P → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ s, load P i j (P.Λ i j * qs i j) s * P.e i j s *
    (g (Sum.inl j) - g (Sum.inr ⟨(i, j), s⟩))

/-- traffic equations of the static network -/
lemma TE (qs : P.L → P.L → ℝ) (hfb : ∀ i, ∑ j, P.Λ i j * qs i j = ∑ j, P.Λ j i * qs j i)
    (g : Slot P → ℝ) : TA qs g + TB qs g + TC qs g = 0 := by
  have per : ∀ i j, P.Λ i j * qs i j *
      ((1 - ∑ s, P.β i j s) * (g (Sum.inl j) - g (Sum.inl i)) +
        ∑ s, P.β i j s * (g (Sum.inr ⟨(i, j), s⟩) - g (Sum.inl i))) +
      (∑ s, ∑ s', if s = s' then 0 else
        load P i j (P.Λ i j * qs i j) s * P.r i j s s' *
          (g (Sum.inr ⟨(i, j), s'⟩) - g (Sum.inr ⟨(i, j), s⟩))) +
      (∑ s, load P i j (P.Λ i j * qs i j) s * P.e i j s *
        (g (Sum.inl j) - g (Sum.inr ⟨(i, j), s⟩))) =
      P.Λ i j * qs i j * (g (Sum.inl j) - g (Sum.inl i)) := by
    intro i j
    have h := stage_ident i j (load P i j (P.Λ i j * qs i j)) (P.Λ i j * qs i j)
      (VSPh.load_balance P i j _) (fun s => g (Sum.inr ⟨(i, j), s⟩)) (g (Sum.inl j))
    have hb : ∑ s, P.β i j s * (g (Sum.inr ⟨(i, j), s⟩) - g (Sum.inl i)) =
        ∑ s, P.β i j s * g (Sum.inr ⟨(i, j), s⟩) - (∑ s, P.β i j s) * g (Sum.inl i) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [hb]
    linear_combination h
  have H : ∑ i, ∑ j, (P.Λ i j * qs i j *
      ((1 - ∑ s, P.β i j s) * (g (Sum.inl j) - g (Sum.inl i)) +
        ∑ s, P.β i j s * (g (Sum.inr ⟨(i, j), s⟩) - g (Sum.inl i))) +
      (∑ s, ∑ s', if s = s' then 0 else
        load P i j (P.Λ i j * qs i j) s * P.r i j s s' *
          (g (Sum.inr ⟨(i, j), s'⟩) - g (Sum.inr ⟨(i, j), s⟩))) +
      (∑ s, load P i j (P.Λ i j * qs i j) s * P.e i j s *
        (g (Sum.inl j) - g (Sum.inr ⟨(i, j), s⟩)))) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => per i j]
    have h1 : ∀ i, ∑ j, P.Λ i j * qs i j * (g (Sum.inl j) - g (Sum.inl i)) =
        ∑ j, P.Λ i j * qs i j * g (Sum.inl j) - (∑ j, P.Λ i j * qs i j) * g (Sum.inl i) := by
      intro i
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, Finset.sum_comm]
    have h2 : ∀ j, ∑ i, P.Λ i j * qs i j * g (Sum.inl j) =
        (∑ i, P.Λ j i * qs j i) * g (Sum.inl j) := by
      intro j
      rw [← Finset.sum_mul, hfb j]
    rw [sum_congr rfl fun j _ => h2 j, sub_self]
  unfold TA TB TC
  simpa only [Finset.sum_add_distrib] using H

/-! ### product-form weights on states -/

/-- relative loads: 1 at every location, the stage loads with entry flow `Λ q` on stages -/
noncomputable def rho (qs : P.L → P.L → ℝ) : Slot P → ℝ
  | Sum.inl _ => 1
  | Sum.inr ⟨p, s⟩ => load P p.1 p.2 (P.Λ p.1 p.2 * qs p.1 p.2) s

noncomputable def wt (qs : P.L → P.L → ℝ) {n : ℕ} (z : State P n) : ℝ :=
  pfWeight (rho qs) isR z.1

/-- add one vehicle at slot `a` -/
def up {n : ℕ} (y : State P n) (a : Slot P) : State P (n + 1) :=
  ⟨y.1 + Pi.single a 1, by
    simp only [Pi.add_apply, Finset.sum_add_distrib, y.2, sum_single_nat]⟩

lemma up_val {n : ℕ} (y : State P n) (a x : Slot P) :
    (up y a).1 x = y.1 x + if x = a then 1 else 0 := by
  simp [up, Pi.single_apply]

lemma mv_val {n : ℕ} (z : State P n) (a b : Slot P) (h : 1 ≤ z.1 a) (x : Slot P) :
    (move z a b).1 x = z.1 x - (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
  unfold move
  rw [dif_pos h]

lemma move_up {n : ℕ} (y : State P n) (a b : Slot P) : move (up y a) a b = up y b := by
  have ha : 1 ≤ (up y a).1 a := by rw [up_val]; simp
  apply Subtype.ext
  funext x
  rw [mv_val _ a b ha, up_val, up_val]
  split_ifs <;> omega

lemma shift_single {n : ℕ} (a : Slot P) (H : State P (n + 1) → ℝ) :
    ∑ z : State P (n + 1), (if 1 ≤ z.1 a then H z else 0) = ∑ y : State P n, H (up y a) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun y _ => up y a)
  · intro y _
    simp [Finset.mem_filter, up_val]
  · intro y1 _ y2 _ h
    apply Subtype.ext
    funext x
    have := congrArg (fun z : State P (n + 1) => z.1 x) h
    simp only [up_val] at this
    omega
  · intro z hz
    have hza : 1 ≤ z.1 a := (Finset.mem_filter.mp hz).2
    refine ⟨⟨fun x => z.1 x - if x = a then 1 else 0, ?_⟩, mem_univ _, ?_⟩
    · have h1 : ∀ x, (z.1 x - if x = a then 1 else 0) + (if x = a then 1 else 0) = z.1 x := by
        intro x
        by_cases hx : x = a
        · subst hx; simp; omega
        · simp [hx]
      have h2 := Finset.sum_congr (s₁ := univ) rfl (fun x (_ : x ∈ univ) => h1 x)
      rw [Finset.sum_add_distrib, z.2] at h2
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
      show ∑ x, (z.1 x - if x = a then 1 else 0) = n
      omega
    · apply Subtype.ext
      funext x
      rw [up_val]
      by_cases hx : x = a
      · subst hx; simp; omega
      · simp [hx]
  · intro y _
    rfl

lemma wshift_single (qs : P.L → P.L → ℝ) {n : ℕ} (a : Slot P) (ha : isR a = false)
    (G : State P (n + 1) → ℝ) :
    ∑ z : State P (n + 1), (if 1 ≤ z.1 a then wt qs z * G z else 0) =
      rho qs a * ∑ y : State P n, wt qs y * G (up y a) := by
  rw [shift_single, Finset.mul_sum]
  refine sum_congr rfl fun y _ => ?_
  have hw : wt qs (up y a) = rho qs a * wt qs y := weight_shift_single (rho qs) isR y.1 a ha
  rw [hw]
  ring

lemma wshift_IS (qs : P.L → P.L → ℝ) {n : ℕ} (a : Slot P) (ha : isR a = true)
    (G : State P (n + 1) → ℝ) :
    ∑ z : State P (n + 1), wt qs z * ((z.1 a : ℝ) * G z) =
      rho qs a * ∑ y : State P n, wt qs y * G (up y a) := by
  have e : ∀ z : State P (n + 1), wt qs z * ((z.1 a : ℝ) * G z) =
      if 1 ≤ z.1 a then wt qs z * ((z.1 a : ℝ) * G z) else 0 := by
    intro z
    split_ifs with h
    · rfl
    · have : z.1 a = 0 := by omega
      simp [this]
  rw [sum_congr rfl fun z _ => e z, shift_single, Finset.mul_sum]
  refine sum_congr rfl fun y _ => ?_
  have hw : wt qs (up y a) * ((y.1 a : ℝ) + 1) = rho qs a * wt qs y :=
    weight_shift_IS (rho qs) isR y.1 a ha
  have hya : ((up y a).1 a : ℝ) = (y.1 a : ℝ) + 1 := by rw [up_val]; simp
  rw [hya]
  linear_combination (G (up y a)) * hw

/-! ### the generator, split into its three parts -/

noncomputable def genA {n : ℕ} (q : State P n → P.L → P.L → ℝ) (f : State P n → ℝ)
    (z : State P n) : ℝ :=
  ∑ i, ∑ j, P.Λ i j * q z i j *
      ((1 - ∑ s, P.β i j s) * (f (move z (Sum.inl i) (Sum.inl j)) - f z)
        + ∑ s, P.β i j s * (f (move z (Sum.inl i) (Sum.inr ⟨(i, j), s⟩)) - f z))

noncomputable def genB {n : ℕ} (f : State P n → ℝ) (z : State P n) : ℝ :=
  ∑ i, ∑ j, ∑ s, ∑ s', if s = s' then 0 else
        (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' *
          (f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inr ⟨(i, j), s'⟩)) - f z)

noncomputable def genC {n : ℕ} (f : State P n → ℝ) (z : State P n) : ℝ :=
  ∑ i, ∑ j, ∑ s, (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s *
        (f (move z (Sum.inr ⟨(i, j), s⟩) (Sum.inl j)) - f z)

lemma gen_eq {n : ℕ} (q : State P n → P.L → P.L → ℝ) (f : State P n → ℝ) (z : State P n) :
    gen q f z = genA q f z + genB f z + genC f z := rfl

lemma comm_z2 {n : ℕ} (F : State P n → P.L → P.L → ℝ) :
    ∑ z, ∑ i, ∑ j, F z i j = ∑ i, ∑ j, ∑ z, F z i j :=
  (Finset.sum_comm).trans (sum_congr rfl fun _ _ => Finset.sum_comm)

lemma comm_z3 {n : ℕ} (F : State P n → ∀ i j : P.L, P.Ph i j → ℝ) :
    ∑ z, ∑ i, ∑ j, ∑ s, F z i j s = ∑ i, ∑ j, ∑ s, ∑ z, F z i j s :=
  (Finset.sum_comm).trans (sum_congr rfl fun _ _ =>
    (Finset.sum_comm).trans (sum_congr rfl fun _ _ => Finset.sum_comm))

lemma comm_z4 {n : ℕ} (F : State P n → ∀ i j : P.L, P.Ph i j → P.Ph i j → ℝ) :
    ∑ z, ∑ i, ∑ j, ∑ s, ∑ s', F z i j s s' = ∑ i, ∑ j, ∑ s, ∑ s', ∑ z, F z i j s s' :=
  (Finset.sum_comm).trans (sum_congr rfl fun _ _ =>
    (Finset.sum_comm).trans (sum_congr rfl fun _ _ =>
      (Finset.sum_comm).trans (sum_congr rfl fun _ _ => Finset.sum_comm)))

section static

variable (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1)

lemma shiftA {n : ℕ} (i j : P.L) (Ψ : State P (n + 1) → ℝ) :
    ∑ z : State P (n + 1), wt qs z * (P.Λ i j * (staticPolicy P (n + 1) qs hqs).1 z i j * Ψ z) =
      ∑ y : State P n, wt qs y * (P.Λ i j * qs i j * Ψ (up y (Sum.inl i))) := by
  have hq : ∀ z : State P (n + 1),
      wt qs z * (P.Λ i j * (staticPolicy P (n + 1) qs hqs).1 z i j * Ψ z) =
        if 1 ≤ z.1 (Sum.inl i) then wt qs z * (P.Λ i j * qs i j * Ψ z) else 0 := by
    intro z
    simp only [staticPolicy]
    split_ifs <;> ring
  rw [sum_congr rfl fun z _ => hq z, wshift_single qs (Sum.inl i) rfl]
  show (1 : ℝ) * _ = _
  rw [one_mul]

lemma shiftB {n : ℕ} (i j : P.L) (s s' : P.Ph i j) (D : State P (n + 1) → ℝ) :
    ∑ z : State P (n + 1), wt qs z * (if s = s' then 0 else
        (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' * D z) =
      ∑ y : State P n, wt qs y * (if s = s' then 0 else
        load P i j (P.Λ i j * qs i j) s * P.r i j s s' * D (up y (Sum.inr ⟨(i, j), s⟩))) := by
  by_cases h : s = s'
  · simp [h]
  · simp only [if_neg h]
    have e : ∀ z : State P (n + 1), wt qs z * ((z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.r i j s s' * D z) =
        wt qs z * ((z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * (P.r i j s s' * D z)) := fun z => by ring
    rw [sum_congr rfl fun z _ => e z, wshift_IS qs (Sum.inr ⟨(i, j), s⟩) rfl, Finset.mul_sum]
    refine sum_congr rfl fun y _ => ?_
    show load P i j (P.Λ i j * qs i j) s * _ = _
    ring

lemma shiftC {n : ℕ} (i j : P.L) (s : P.Ph i j) (D : State P (n + 1) → ℝ) :
    ∑ z : State P (n + 1), wt qs z * ((z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s * D z) =
      ∑ y : State P n, wt qs y *
        (load P i j (P.Λ i j * qs i j) s * P.e i j s * D (up y (Sum.inr ⟨(i, j), s⟩))) := by
  have e : ∀ z : State P (n + 1), wt qs z * ((z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * P.e i j s * D z) =
      wt qs z * ((z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * (P.e i j s * D z)) := fun z => by ring
  rw [sum_congr rfl fun z _ => e z, wshift_IS qs (Sum.inr ⟨(i, j), s⟩) rfl, Finset.mul_sum]
  refine sum_congr rfl fun y _ => ?_
  show load P i j (P.Λ i j * qs i j) s * _ = _
  ring

lemma PA {n : ℕ} (f : State P (n + 1) → ℝ) :
    ∑ z : State P (n + 1), wt qs z * genA (staticPolicy P (n + 1) qs hqs).1 f z =
      ∑ y : State P n, wt qs y * TA qs (fun b => f (up y b)) := by
  simp only [genA, TA, Finset.mul_sum]
  rw [comm_z2, comm_z2]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [shiftA qs hqs i j]
  refine sum_congr rfl fun y _ => ?_
  simp only [move_up]

lemma PB {n : ℕ} (f : State P (n + 1) → ℝ) :
    ∑ z : State P (n + 1), wt qs z * genB f z =
      ∑ y : State P n, wt qs y * TB qs (fun b => f (up y b)) := by
  simp only [genB, TB, Finset.mul_sum]
  rw [comm_z4, comm_z4]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun s _ =>
    sum_congr rfl fun s' _ => ?_
  rw [shiftB qs i j s s']
  refine sum_congr rfl fun y _ => ?_
  simp only [move_up]

lemma PC {n : ℕ} (f : State P (n + 1) → ℝ) :
    ∑ z : State P (n + 1), wt qs z * genC f z =
      ∑ y : State P n, wt qs y * TC qs (fun b => f (up y b)) := by
  simp only [genC, TC, Finset.mul_sum]
  rw [comm_z3, comm_z3]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun s _ => ?_
  rw [shiftC qs i j s]
  refine sum_congr rfl fun y _ => ?_
  simp only [move_up]

theorem gen_weighted_zero (hfb : ∀ i, ∑ j, P.Λ i j * qs i j = ∑ j, P.Λ j i * qs j i)
    {n : ℕ} (f : State P (n + 1) → ℝ) :
    ∑ z : State P (n + 1), wt qs z * gen (staticPolicy P (n + 1) qs hqs).1 f z = 0 := by
  simp only [gen_eq, mul_add, Finset.sum_add_distrib]
  rw [PA qs hqs, PB qs, PC qs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [← mul_add, ← mul_add, TE qs hfb, mul_zero]

end static


section stat2

variable (qs : P.L → P.L → ℝ)

lemma rho_nonneg (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1) (s : Slot P) : 0 ≤ rho qs s := by
  rcases s with i | ⟨⟨i, j⟩, s⟩
  · show (0 : ℝ) ≤ 1
    norm_num
  · exact load_nonneg P i j _ (mul_nonneg (P.Λ_nonneg i j) (hqs i j).1) s

lemma wt_nonneg (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1) {n : ℕ} (z : State P n) : 0 ≤ wt qs z := by
  unfold wt pfWeight
  apply Finset.prod_nonneg
  intro s _
  split_ifs
  · exact div_nonneg (pow_nonneg (rho_nonneg qs hqs s) _) (Nat.cast_nonneg _)
  · exact pow_nonneg (rho_nonneg qs hqs s) _

lemma sum_wt (n : ℕ) : ∑ z : State P n, wt qs z = pfNormConst (rho qs) isR n := by
  unfold pfNormConst
  apply Finset.sum_bij (fun z _ => z.1)
  · intro z _
    exact (mem_popStates n z.1).mpr z.2
  · intro a _ b _ h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x, (mem_popStates n x).mp hx⟩, mem_univ _, rfl⟩
  · intro z _
    rfl

lemma G_pos (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1) [Nonempty P.L] (n : ℕ) : 0 < pfNormConst (rho qs) isR n :=
  normConst_pos (rho qs) isR (rho_nonneg qs hqs) (Sum.inl (Classical.arbitrary P.L)) rfl
    (by show (0 : ℝ) < 1; norm_num) n

/-- S4: the product form is a stationary law of the static chain -/
theorem pf_stationary (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1) [Nonempty P.L]
    (hfb : ∀ i, ∑ j, P.Λ i j * qs i j = ∑ j, P.Λ j i * qs j i) (K : ℕ) :
    IsStationary (staticPolicy P K qs hqs) (fun z => wt qs z / pfNormConst (rho qs) isR K) := by
  have hG := G_pos qs hqs K
  refine ⟨fun z => div_nonneg (wt_nonneg qs hqs z) hG.le, ?_, fun f => ?_⟩
  · show ∑ z, wt qs z / pfNormConst (rho qs) isR K = 1
    rw [← Finset.sum_div, sum_wt, div_self hG.ne']
  · show ∑ z, wt qs z / pfNormConst (rho qs) isR K * gen (staticPolicy P K qs hqs).1 f z = 0
    have e : ∀ z, wt qs z / pfNormConst (rho qs) isR K * gen (staticPolicy P K qs hqs).1 f z =
        (wt qs z * gen (staticPolicy P K qs hqs).1 f z) / pfNormConst (rho qs) isR K :=
      fun z => by ring
    rw [sum_congr rfl fun z _ => e z, ← Finset.sum_div]
    cases K with
    | zero =>
      have h0 : ∀ z : State P 0, gen (staticPolicy P 0 qs hqs).1 f z = 0 := by
        intro z
        have hz : ∀ x, z.1 x = 0 := fun x => by
          have := Finset.single_le_sum (f := z.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
          rw [z.2] at this
          omega
        simp [gen, staticPolicy, hz]
      simp [h0]
    | succ n => rw [gen_weighted_zero qs hqs hfb f, zero_div]

end stat2

end VSPF
-- G_main: body only; follows A_pf, C_prop1, D_flux, E_reach, F_pf.

namespace VSMain

open Finset VehicleSharePricing.Static VehShare.MultiNet VSAux VSPF
open VehShare.SeqBounds (Bseq)

variable {P : Instance} {K : ℕ}

lemma avail (qs : P.L → P.L → ℝ) (i : P.L) :
    ∑ z : State P K, (if 1 ≤ z.1 (Sum.inl i) then wt qs z / pfNormConst (rho qs) isR K else 0) =
      pfBusyProb (rho qs) isR K (Sum.inl i) := by
  unfold pfBusyProb pfProb
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun z _ => z.1)
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(mem_popStates K z.1).mpr z.2, (Finset.mem_filter.mp hz).2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨⟨x, (mem_popStates K x).mp hx'.1⟩, Finset.mem_filter.mpr ⟨mem_univ _, hx'.2⟩, rfl⟩
  · intro z _
    rfl

lemma reward_pf (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1) :
    reward (staticPolicy P K qs hqs) (fun z => wt qs z / pfNormConst (rho qs) isR K) =
      ∑ i, pfBusyProb (rho qs) isR K (Sum.inl i) * ∑ j, P.Λ i j * qs i j * P.I i j (qs i j) := by
  unfold reward
  have e : ∀ z : State P K, wt qs z / pfNormConst (rho qs) isR K *
      ∑ i, ∑ j, P.Λ i j * (staticPolicy P K qs hqs).1 z i j * P.I i j ((staticPolicy P K qs hqs).1 z i j) =
      ∑ i, (if 1 ≤ z.1 (Sum.inl i) then wt qs z / pfNormConst (rho qs) isR K else 0) *
        ∑ j, P.Λ i j * qs i j * P.I i j (qs i j) := by
    intro z
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : 1 ≤ z.1 (Sum.inl i)
    · simp [staticPolicy, h]
    · simp [staticPolicy, h]
  rw [sum_congr rfl fun z _ => e z, Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, avail]

lemma Rs_nonneg (Δ : ℝ) (hΔ : (K : ℝ) ≤ Δ) (qs : P.L → P.L → ℝ) (hqs : IsOptimal2 P Δ qs) :
    0 ≤ Rs P qs := by
  have h0 : IsFeasible2 P Δ (fun _ _ => 0) := by
    refine ⟨fun i j => ⟨le_refl _, zero_le_one⟩, fun i => by simp, ?_⟩
    simp only [workload, mul_zero, zero_mul, Finset.sum_const_zero]
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  have := hqs.2 _ h0
  simpa [Rs] using this

lemma workload_nonneg (qs : P.L → P.L → ℝ) (hb : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1) :
    0 ≤ workload P qs :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (P.Λ_nonneg i j) (hb i j).1) (VSPh.meanTime_nonneg P i j)

lemma workload_le (qs : P.L → P.L → ℝ) (hb : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1) :
    workload P qs ≤ LamOverMu P :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
    have hm := mul_nonneg (P.Λ_nonneg i j) (VSPh.meanTime_nonneg P i j)
    calc P.Λ i j * qs i j * meanTime P i j = (P.Λ i j * meanTime P i j) * qs i j := by ring
      _ ≤ (P.Λ i j * meanTime P i j) * 1 := mul_le_mul_of_nonneg_left (hb i j).2 hm
      _ = P.Λ i j * meanTime P i j := by ring

lemma Bseq_lower (N : ℕ) (hN : 1 ≤ N) (W : ℝ) (hW : 0 ≤ W) (K i : ℕ) (hi : 1 ≤ i) (hK : 1 ≤ K) :
    (K : ℝ) / ((N : ℝ) + (K : ℝ) - 1 + W) ≤ Bseq N W K i := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [Bseq_succ]
  have hm := Bseq_mem N hN W hW i' (K - 1)
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : 0 ≤ W * (1 - Bseq N W (K - 1) i') := mul_nonneg hW (sub_nonneg.mpr hm.2)
  have h2 : 0 ≤ W * Bseq N W (K - 1) i' := mul_nonneg hW hm.1
  apply div_le_div_of_nonneg_left (by positivity)
  · linarith
  · linarith

lemma Bseq_le_KK (N : ℕ) (hN : 1 ≤ N) (W : ℝ) (hW : 0 ≤ W) (K i : ℕ) (hi : i ≤ K) :
    Bseq N W K i ≤ Bseq N W K K :=
  monotone_nat_of_le_succ (fun n => Bseq_mono_succ N hN W hW n K) hi

end VSMain


/-! ## Multi-network part: allocation classes of the static chain -/

namespace VSMulti

open Finset VehicleSharePricing.Static VehShare.MultiNet VSAux VSFlux VSReach VSPF
open VehShare.SeqBounds (Bseq)

variable {P : Instance} {K : ℕ}

lemma pos_left {a b : ℝ} (ha : 0 ≤ a) (h : 0 < a * b) : 0 < a := by
  rcases ha.eq_or_lt with h0 | h0
  · rw [← h0, zero_mul] at h
    exact absurd h (lt_irrefl 0)
  · exact h0

/-- `gen` only sees the values at `z` and at its positive-rate successors -/
lemma gen_congr (q : Policy P K) (g h : State P K → ℝ) (z : State P K) (hz : g z = h z)
    (hs : ∀ w, Step q z w → g w = h w) : gen q.1 g z = gen q.1 h z := by
  have hd : ∀ w, Step q z w → g w - g z = h w - h z := fun w hw => by rw [hs w hw, hz]
  unfold gen
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases (mul_nonneg (P.Λ_nonneg i j) (q.2.1 z i j).1).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, zero_mul]
    · congr 1
      congr 1
      · rcases (one_sub_beta i j).eq_or_lt with h1 | h1
        · rw [← h1, zero_mul, zero_mul]
        · rw [hd _ (Or.inl ⟨i, j, mul_pos h0 h1, rfl⟩)]
      · refine Finset.sum_congr rfl fun s _ => ?_
        rcases (P.β_nonneg i j s).eq_or_lt with h1 | h1
        · rw [← h1, zero_mul, zero_mul]
        · rw [hd _ (Or.inr (Or.inl ⟨i, j, s, mul_pos h0 h1, rfl⟩))]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    split_ifs with hss
    · rfl
    · rcases (mul_nonneg (Nat.cast_nonneg (z.1 (Sum.inr ⟨(i, j), s⟩)))
          (P.r_nonneg i j s s')).eq_or_lt with h1 | h1
      · rw [← h1, zero_mul, zero_mul]
      · rw [hd _ (Or.inr (Or.inr (Or.inl ⟨i, j, s, s', hss, h1, rfl⟩)))]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun s _ => ?_
    rcases (mul_nonneg (Nat.cast_nonneg (z.1 (Sum.inr ⟨(i, j), s⟩)))
        (P.e_nonneg i j s)).eq_or_lt with h1 | h1
    · rw [← h1, zero_mul, zero_mul]
    · rw [hd _ (Or.inr (Or.inr (Or.inr ⟨i, j, s, h1, rfl⟩)))]

/-! ### balanced flow: every live edge lies on a live cycle -/

lemma live_back (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1)
    (hfb : ∀ i, ∑ j, P.Λ i j * qs i j = ∑ j, P.Λ j i * qs j i)
    {i j : P.L} (h : live P qs i j) : Relation.ReflTransGen (live P qs) j i := by
  classical
  by_contra hji
  set R := (univ : Finset P.L).filter (fun x => Relation.ReflTransGen (live P qs) j x) with hR
  have hiR : i ∉ R := by simp [hR, hji]
  have hjR : j ∈ R := by
    rw [hR, mem_filter]; exact ⟨mem_univ _, Relation.ReflTransGen.refl⟩
  have hclosed : ∀ x ∈ R, ∀ y, live P qs x y → y ∈ R := by
    intro x hx y hxy
    simp only [hR, mem_filter, mem_univ, true_and] at hx ⊢
    exact hx.tail hxy
  have hf0 : ∀ x y, 0 ≤ P.Λ x y * qs x y := fun x y => mul_nonneg (P.Λ_nonneg x y) (hqs x y).1
  have hbal : ∑ x ∈ R, ∑ y, P.Λ x y * qs x y = ∑ x ∈ R, ∑ y, P.Λ y x * qs y x :=
    Finset.sum_congr rfl fun x _ => hfb x
  have hout : ∀ x ∈ R, ∑ y, P.Λ x y * qs x y = ∑ y ∈ R, P.Λ x y * qs x y := by
    intro x hx
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun y => y ∈ R)]
    have : ∑ y ∈ univ.filter (fun y => y ∉ R), P.Λ x y * qs x y = 0 := by
      refine Finset.sum_eq_zero fun y hy => ?_
      have hyR : y ∉ R := (mem_filter.mp hy).2
      rcases (hf0 x y).eq_or_lt with h0 | h0
      · exact h0.symm
      · exact absurd (hclosed x hx y h0) hyR
    rw [this, add_zero, Finset.filter_mem_eq_inter, univ_inter]
  have hin : ∀ x ∈ R, ∑ y, P.Λ y x * qs y x =
      ∑ y ∈ R, P.Λ y x * qs y x + ∑ y ∈ univ.filter (fun y => y ∉ R), P.Λ y x * qs y x := by
    intro x _
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun y => y ∈ R), Finset.filter_mem_eq_inter,
      univ_inter]
  rw [Finset.sum_congr rfl hout, Finset.sum_congr rfl hin, Finset.sum_add_distrib] at hbal
  have hcomm : ∑ x ∈ R, ∑ y ∈ R, P.Λ x y * qs x y = ∑ x ∈ R, ∑ y ∈ R, P.Λ y x * qs y x :=
    Finset.sum_comm
  have hpos : 0 < ∑ x ∈ R, ∑ y ∈ univ.filter (fun y => y ∉ R), P.Λ y x * qs y x := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun x => ∑ y ∈ univ.filter (fun y => y ∉ R), P.Λ y x * qs y x)
      (fun x _ => Finset.sum_nonneg fun y _ => hf0 y x) hjR)
    exact lt_of_lt_of_le h (Finset.single_le_sum (f := fun y => P.Λ y j * qs y j)
      (fun y _ => hf0 y j) (mem_filter.mpr ⟨mem_univ i, hiR⟩))
  linarith

lemma comp_eq_of_live (qs : P.L → P.L → ℝ) {i j : P.L} (h : live P qs i j) :
    (flowGraph P qs).connectedComponentMk i = (flowGraph P qs).connectedComponentMk j := by
  by_cases hij : i = j
  · rw [hij]
  · exact SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable
      (by simp only [flowGraph, SimpleGraph.fromRel_adj]; exact ⟨hij, Or.inl h⟩))

lemma comp_reach (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1)
    (hfb : ∀ i, ∑ j, P.Λ i j * qs i j = ∑ j, P.Λ j i * qs j i) {a b : P.L}
    (h : (flowGraph P qs).connectedComponentMk a = (flowGraph P qs).connectedComponentMk b) :
    Relation.ReflTransGen (live P qs) a b := by
  rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
    refine ih.trans ?_
    simp only [flowGraph, SimpleGraph.fromRel_adj] at hcd
    rcases hcd.2 with h' | h'
    · exact Relation.ReflTransGen.single h'
    · exact live_back qs hqs hfb h'

/-! ### representatives and reachability inside a class -/

noncomputable def mcRep (qs : P.L → P.L → ℝ) (c : (flowGraph P qs).ConnectedComponent) : P.L :=
  Quot.out c

lemma comp_rep (qs : P.L → P.L → ℝ) (c : (flowGraph P qs).ConnectedComponent) :
    (flowGraph P qs).connectedComponentMk (mcRep qs c) = c :=
  Quot.out_eq c

def mcEnd : Slot P → P.L
  | Sum.inl i => i
  | Sum.inr ⟨p, _⟩ => p.2

noncomputable def mcTgt (qs : P.L → P.L → ℝ) (x : Slot P) : Slot P :=
  Sum.inl (mcRep qs ((flowGraph P qs).connectedComponentMk (mcEnd x)))

def mcIsRep (qs : P.L → P.L → ℝ) (x : Slot P) : Prop :=
  ∃ c, x = Sum.inl (mcRep qs c)

lemma tgt_rep (qs : P.L → P.L → ℝ) (x : Slot P) : mcIsRep qs (mcTgt qs x) := ⟨_, rfl⟩

lemma slot_tgt (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1)
    (hfb : ∀ i, ∑ j, P.Λ i j * qs i j = ∑ j, P.Λ j i * qs j i) (x : Slot P) :
    Relation.ReflTransGen (SlotStep (staticPolicy P K qs hqs)) x (mcTgt qs x) := by
  have loc : ∀ i, Relation.ReflTransGen (SlotStep (staticPolicy P K qs hqs)) (Sum.inl i)
      (Sum.inl (mcRep qs ((flowGraph P qs).connectedComponentMk i))) := fun i =>
    Relation.ReflTransGen.lift' (fun y => (Sum.inl y : Slot P))
      (fun a b hab => edge_reach qs hqs a b hab) _ _ (comp_reach qs hqs hfb (comp_rep qs _).symm)
  rcases x with i | ⟨⟨i, j⟩, s⟩
  · exact loc i
  · exact (stage_reach qs hqs i j s).trans (loc j)

lemma reach_reps (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1)
    (hfb : ∀ i, ∑ j, P.Λ i j * qs i j = ∑ j, P.Λ j i * qs j i) (z : State P K) :
    ∃ w, Relation.ReflTransGen (Step (staticPolicy P K qs hqs)) z w ∧
      ∀ x, ¬ mcIsRep qs x → w.1 x = 0 := by
  classical
  suffices H : ∀ n : ℕ, ∀ z : State P K,
      ∑ x ∈ univ.filter (fun x => ¬ mcIsRep qs x), z.1 x = n →
      ∃ w, Relation.ReflTransGen (Step (staticPolicy P K qs hqs)) z w ∧
        ∀ x, ¬ mcIsRep qs x → w.1 x = 0 from H _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hn
    by_cases hall : ∀ x, ¬ mcIsRep qs x → z.1 x = 0
    · exact ⟨z, Relation.ReflTransGen.refl, hall⟩
    · push Not at hall
      obtain ⟨a, ha, hza⟩ := hall
      have hza1 : 1 ≤ z.1 a := Nat.one_le_iff_ne_zero.mpr hza
      have hR := lift _ (slot_tgt qs hqs hfb a) z hza1
      have haS : a ∈ univ.filter (fun x => ¬ mcIsRep qs x) := mem_filter.mpr ⟨mem_univ a, ha⟩
      have hat : a ≠ mcTgt qs a := fun h => ha (by rw [h]; exact tgt_rep qs a)
      have hsum : ∑ x ∈ univ.filter (fun x => ¬ mcIsRep qs x), (move z a (mcTgt qs a)).1 x + 1 =
          ∑ x ∈ univ.filter (fun x => ¬ mcIsRep qs x), z.1 x := by
        rw [← Finset.add_sum_erase _ _ haS, ← Finset.add_sum_erase _ (fun x => z.1 x) haS]
        have e1 : (move z a (mcTgt qs a)).1 a = z.1 a - 1 := by
          rw [move_val z a _ hza1]
          simp [hat]
        have e2 : ∑ x ∈ (univ.filter (fun x => ¬ mcIsRep qs x)).erase a, (move z a (mcTgt qs a)).1 x =
            ∑ x ∈ (univ.filter (fun x => ¬ mcIsRep qs x)).erase a, z.1 x := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hxa : x ≠ a := Finset.ne_of_mem_erase hx
          have hxb : x ≠ mcTgt qs a := fun h =>
            (mem_filter.mp (Finset.mem_of_mem_erase hx)).2 (by rw [h]; exact tgt_rep qs a)
          rw [move_val z a _ hza1]
          simp [hxa, hxb]
        rw [e1, e2]
        omega
      obtain ⟨w, hw, hw0⟩ := ih _ (by omega) (move z a (mcTgt qs a)) rfl
      exact ⟨w, hR.trans hw, hw0⟩

lemma vin_rep (qs : P.L → P.L → ℝ) (w : State P K) (hw : ∀ x, ¬ mcIsRep qs x → w.1 x = 0)
    (c : (flowGraph P qs).ConnectedComponent) :
    vehiclesIn P qs c w = w.1 (Sum.inl (mcRep qs c)) := by
  classical
  unfold vehiclesIn
  have htr : ∀ i j (s : P.Ph i j), w.1 (Sum.inr ⟨(i, j), s⟩) = 0 := fun i j s =>
    hw _ (by rintro ⟨c', h⟩; cases h)
  rw [Finset.sum_eq_single (mcRep qs c)]
  · rw [Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero fun s _ => htr _ j s), add_zero]
  · intro i hi hne
    have h1 : w.1 (Sum.inl i) = 0 := hw _ (by
      rintro ⟨c', h⟩
      have hi' : i = mcRep qs c' := Sum.inl_injective h
      have := (mem_filter.mp hi).2
      rw [hi', comp_rep] at this
      exact hne (by rw [hi', this]))
    rw [h1, zero_add]
    exact Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun s _ => htr _ j s
  · intro h
    exact absurd (mem_filter.mpr ⟨mem_univ (mcRep qs c), comp_rep qs c⟩) h

lemma reps_unique (qs : P.L → P.L → ℝ) (Kc : (flowGraph P qs).ConnectedComponent → ℕ)
    (w w' : State P K) (hw : ∀ x, ¬ mcIsRep qs x → w.1 x = 0)
    (hw' : ∀ x, ¬ mcIsRep qs x → w'.1 x = 0) (ha : OnAllocation P qs Kc w)
    (ha' : OnAllocation P qs Kc w') : w = w' := by
  apply Subtype.ext
  funext x
  by_cases hx : mcIsRep qs x
  · obtain ⟨c, rfl⟩ := hx
    rw [← vin_rep qs w hw c, ← vin_rep qs w' hw' c, ha.2 c, ha'.2 c]
  · rw [hw x hx, hw' x hx]

lemma supp_path (q : Policy P K) (π : State P K → ℝ) (hπ : IsStationary q π) {z w : State P K}
    (h : Relation.ReflTransGen (Step q) z w) (hz : 0 < π z) : 0 < π w := by
  induction h with
  | refl => exact hz
  | @tail b c _ hbc ih => exact supp_closed q π hπ b c hbc ih

/-- inside the support of a stationary law, every path can be walked back -/
lemma supp_back (q : Policy P K) (π : State P K → ℝ) (hπ : IsStationary q π) {z w : State P K}
    (hpath : Relation.ReflTransGen (Step q) z w) (hz : 0 < π z) :
    Relation.ReflTransGen (Step q) w z := by
  classical
  set T : State P K → Prop := fun x => Relation.ReflTransGen (Step q) w x with hT
  set f : State P K → ℝ := fun x => if T x then 1 else 0 with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; split_ifs <;> norm_num
  have hterm : ∀ x ∈ (univ : Finset (State P K)), 0 ≤ π x * gen q.1 f x := by
    intro x _
    by_cases hx : T x
    · have : gen q.1 f x = 0 := gen_zero_of_const q f x (fun v hv => by
        have hv' : T v := Relation.ReflTransGen.tail hx hv
        simp only [hf, if_pos hv', if_pos hx])
      rw [this, mul_zero]
    · exact mul_nonneg (hπ.1 x) (gen_nonneg_of_zero q f hf0 x (by simp only [hf, if_neg hx]))
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp (hπ.2.2 f)
  have key : ∀ x, 0 < π x → ¬ T x → ∀ v, Step q x v → ¬ T v := by
    intro x hx hxT v hs hvT
    have hg : gen q.1 f x = 0 := by
      rcases mul_eq_zero.mp (hall x (mem_univ x)) with h | h
      · linarith
      · exact h
    have := step_zero q f hf0 x (by simp only [hf, if_neg hxT]) hg.le v hs
    simp only [hf, if_pos hvT] at this
    exact one_ne_zero this
  by_contra hzT
  have : ∀ y, Relation.ReflTransGen (Step q) z y → 0 < π y ∧ ¬ T y := by
    intro y hy
    induction hy with
    | refl => exact ⟨hz, hzT⟩
    | @tail b c _ hbc ih =>
      exact ⟨supp_closed q π hπ b c hbc ih.1, key b ih.1 ih.2 c hbc⟩
  exact (this _ hpath).2 Relation.ReflTransGen.refl

/-- the static chain has at most one stationary law on each allocation class -/
theorem stat_unique_class (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1)
    (hfb : ∀ i, ∑ j, P.Λ i j * qs i j = ∑ j, P.Λ j i * qs j i)
    (Kc : (flowGraph P qs).ConnectedComponent → ℕ) (π π' : State P K → ℝ)
    (hπ : IsStationary (staticPolicy P K qs hqs) π) (hπ' : IsStationary (staticPolicy P K qs hqs) π')
    (hc : ConcentratedOn P qs Kc π) (hc' : ConcentratedOn P qs Kc π') : π = π' := by
  classical
  set S := (univ : Finset (State P K)).filter (fun z => 0 < π' z) with hSdef
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h0 : ∀ z, π' z = 0 := fun z => by
      by_contra hz
      have hm : z ∈ S := Finset.mem_filter.mpr ⟨mem_univ z, lt_of_le_of_ne (hπ'.1 z) (Ne.symm hz)⟩
      rw [hne] at hm
      simp at hm
    have := hπ'.2.1
    simp [h0] at this
  obtain ⟨z1, hz1S, hmin⟩ := Finset.exists_min_image S (fun z => π z / π' z) hSne
  have hz1 : 0 < π' z1 := (Finset.mem_filter.mp hz1S).2
  set t := π z1 / π' z1 with htdef
  set v : State P K → ℝ := fun z => t * π' z - π z with hvdef
  have hle : ∀ z, v z ≤ 0 := by
    intro z
    simp only [hvdef]
    by_cases hz : 0 < π' z
    · have := hmin z (Finset.mem_filter.mpr ⟨mem_univ z, hz⟩)
      rw [le_div_iff₀ hz] at this
      linarith
    · have : π' z = 0 := le_antisymm (not_lt.mp hz) (hπ'.1 z)
      rw [this, mul_zero]
      linarith [hπ.1 z]
  have hv : ∀ f : State P K → ℝ, ∑ z, v z * gen (staticPolicy P K qs hqs).1 f z = 0 := by
    intro f
    have e : ∀ z, v z * gen (staticPolicy P K qs hqs).1 f z =
        t * (π' z * gen (staticPolicy P K qs hqs).1 f z) - π z * gen (staticPolicy P K qs hqs).1 f z :=
      fun z => by simp only [hvdef]; ring
    rw [Finset.sum_congr rfl (fun z _ => e z), Finset.sum_sub_distrib, ← Finset.mul_sum,
      hπ.2.2 f, hπ'.2.2 f]
    ring
  have hvz1 : v z1 = 0 := by
    show t * π' z1 - π z1 = 0
    rw [htdef, div_mul_cancel₀ _ hz1.ne', sub_self]
  obtain ⟨w1, hz1w1, hw1⟩ := reach_reps qs hqs hfb z1
  have hw1A : OnAllocation P qs Kc w1 := hc' w1 (supp_path _ π' hπ' hz1w1 hz1).ne'
  have hvw1 : v w1 = 0 := back_zero _ v hv hle (supp_back _ π' hπ' hz1w1 hz1) hvz1
  have hvall : ∀ z, v z = 0 := by
    intro z
    by_cases h0 : π z = 0 ∧ π' z = 0
    · show t * π' z - π z = 0
      rw [h0.1, h0.2]
      ring
    · obtain ⟨wz, hzw, hwz⟩ := reach_reps qs hqs hfb z
      have hwzA : OnAllocation P qs Kc wz := by
        rcases not_and_or.mp h0 with h | h
        · exact hc wz (supp_path _ π hπ hzw (lt_of_le_of_ne (hπ.1 z) (Ne.symm h))).ne'
        · exact hc' wz (supp_path _ π' hπ' hzw (lt_of_le_of_ne (hπ'.1 z) (Ne.symm h))).ne'
      rw [reps_unique qs Kc wz w1 hwz hw1 hwzA hw1A] at hzw
      exact back_zero _ v hv hle hzw hvw1
  have h1 : ∑ z, v z = t * ∑ z, π' z - ∑ z, π z := by
    simp only [hvdef]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hπ.2.1, hπ'.2.1, Finset.sum_eq_zero (fun z _ => hvall z)] at h1
  have ht : t = 1 := by linarith
  funext z
  have := hvall z
  simp only [hvdef, ht, one_mul] at this
  linarith

/-! ### vehicle counts are invariant under the static chain -/

open Classical in
noncomputable def mcCnt (qs : P.L → P.L → ℝ) (c : (flowGraph P qs).ConnectedComponent) :
    Slot P → ℝ
  | Sum.inl i => if (flowGraph P qs).connectedComponentMk i = c then 1 else 0
  | Sum.inr ⟨p, _⟩ =>
    if (flowGraph P qs).connectedComponentMk p.1 = c ∧ live P qs p.1 p.2 then 1 else 0

lemma vin_cast (qs : P.L → P.L → ℝ) (c : (flowGraph P qs).ConnectedComponent) (z : State P K) :
    (vehiclesIn P qs c z : ℝ) = VSProp1.linF (mcCnt qs c) z := by
  classical
  unfold vehiclesIn VSProp1.linF
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hc : (flowGraph P qs).connectedComponentMk i = c
  · rw [if_pos hc, Finset.sum_filter]
    simp only [mcCnt, hc, true_and, if_true, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hl : live P qs i j <;> simp [hl]
  · rw [if_neg hc]
    simp [mcCnt, hc]

lemma alloc_step (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1) (z w : State P K)
    (hz : ∀ i j (s : P.Ph i j), ¬ live P qs i j → z.1 (Sum.inr ⟨(i, j), s⟩) = 0)
    (hs : Step (staticPolicy P K qs hqs) z w) (c : (flowGraph P qs).ConnectedComponent) :
    vehiclesIn P qs c w = vehiclesIn P qs c z := by
  have key : ∀ a b, 1 ≤ z.1 a → w = move z a b → mcCnt qs c a = mcCnt qs c b →
      vehiclesIn P qs c w = vehiclesIn P qs c z := by
    intro a b ha hw hab
    have h1 := VSProp1.linF_move (mcCnt qs c) z a b ha
    rw [← hw, ← vin_cast, ← vin_cast, hab, sub_self] at h1
    exact_mod_cast sub_eq_zero.mp h1
  have hq : ∀ i j, 0 < P.Λ i j * (staticPolicy P K qs hqs).1 z i j →
      1 ≤ z.1 (Sum.inl i) ∧ live P qs i j := by
    intro i j h
    by_cases hi : 1 ≤ z.1 (Sum.inl i)
    · rw [static_q qs hqs z i j hi] at h
      exact ⟨hi, h⟩
    · rw [show (staticPolicy P K qs hqs).1 z i j = 0 by simp [staticPolicy, hi], mul_zero] at h
      exact absurd h (lt_irrefl 0)
  have hnn : ∀ i j, 0 ≤ P.Λ i j * (staticPolicy P K qs hqs).1 z i j := fun i j =>
    mul_nonneg (P.Λ_nonneg i j) (((staticPolicy P K qs hqs).2.1 z i j).1)
  have hocc : ∀ (i j : P.L) (s : P.Ph i j) (x : ℝ), 0 ≤ x →
      0 < (z.1 (Sum.inr ⟨(i, j), s⟩) : ℝ) * x → 1 ≤ z.1 (Sum.inr ⟨(i, j), s⟩) := by
    intro i j s x _ h
    have h' := pos_left (Nat.cast_nonneg _) h
    have : 0 < z.1 (Sum.inr ⟨(i, j), s⟩) := by exact_mod_cast h'
    omega
  rcases hs with ⟨i, j, h, rfl⟩ | ⟨i, j, s, h, rfl⟩ | ⟨i, j, s, s', _, h, rfl⟩ | ⟨i, j, s, h, rfl⟩
  · obtain ⟨hi, hl⟩ := hq i j (pos_left (hnn i j) h)
    refine key _ _ hi rfl ?_
    simp only [mcCnt]
    rw [comp_eq_of_live qs hl]
  · obtain ⟨hi, hl⟩ := hq i j (pos_left (hnn i j) h)
    refine key _ _ hi rfl ?_
    simp only [mcCnt]
    by_cases hc : (flowGraph P qs).connectedComponentMk i = c
    · rw [if_pos hc, if_pos ⟨hc, hl⟩]
    · rw [if_neg hc, if_neg (fun h => hc h.1)]
  · exact key _ _ (hocc i j s _ (P.r_nonneg i j s s') h) rfl (by simp only [mcCnt])
  · have ho := hocc i j s _ (P.e_nonneg i j s) h
    have hl : live P qs i j := by
      by_contra hl
      have := hz i j s hl
      omega
    refine key _ _ ho rfl ?_
    simp only [mcCnt]
    rw [comp_eq_of_live qs hl]
    by_cases hc : (flowGraph P qs).connectedComponentMk j = c
    · rw [if_pos hc, if_pos ⟨hc, hl⟩]
    · rw [if_neg hc, if_neg (fun h => hc h.1)]

lemma sum_alloc (qs : P.L → P.L → ℝ) (Kc : (flowGraph P qs).ConnectedComponent → ℕ)
    (z : State P K) (hz : OnAllocation P qs Kc z) : ∑ c, Kc c = K := by
  refine (Finset.sum_congr rfl fun c _ => (hz.2 c).symm).trans ?_
  classical
  unfold vehiclesIn
  refine Eq.trans (b := ∑ i, ((z.1 (Sum.inl i) : ℕ) +
    ∑ j ∈ univ.filter (fun j => live P qs i j), ∑ s, z.1 (Sum.inr ⟨(i, j), s⟩))) ?_ ?_
  · convert Finset.sum_fiberwise (univ : Finset P.L) (flowGraph P qs).connectedComponentMk _
  have h2 : ∀ i, ∑ j ∈ univ.filter (fun j => live P qs i j), ∑ s, z.1 (Sum.inr ⟨(i, j), s⟩) =
      ∑ j, ∑ s, z.1 (Sum.inr ⟨(i, j), s⟩) := fun i =>
    Finset.sum_filter_of_ne fun j _ hne => by
      by_contra hl
      exact hne (Finset.sum_eq_zero fun s _ => hz.1 i j s hl)
  simp only [h2]
  have := z.2
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_prod_type] at this
  rw [Finset.sum_add_distrib]
  exact this

/-! ### the product form, its classes and the averaging step -/

noncomputable def mcPis (qs : P.L → P.L → ℝ) (K : ℕ) (z : State P K) : ℝ :=
  VSPF.wt qs z / pfNormConst (VSPF.rho qs) VSAux.isR K

noncomputable def mcRew (q : Policy P K) (z : State P K) : ℝ :=
  ∑ i, ∑ j, P.Λ i j * q.1 z i j * P.I i j (q.1 z i j)

lemma reward_eq (q : Policy P K) (π : State P K → ℝ) : reward q π = ∑ z, π z * mcRew q z := rfl

lemma wt_nonlive (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1) {n : ℕ}
    (z : State P n) (hz : VSPF.wt qs z ≠ 0) (i j : P.L) (s : P.Ph i j) (hl : ¬ live P qs i j) :
    z.1 (Sum.inr ⟨(i, j), s⟩) = 0 := by
  by_contra hne
  apply hz
  unfold VSPF.wt pfWeight
  apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inr ⟨(i, j), s⟩ : Slot P))
  have h0 : P.Λ i j * qs i j = 0 :=
    le_antisymm (not_lt.mp hl) (mul_nonneg (P.Λ_nonneg i j) (hqs i j).1)
  have hr : VSPF.rho qs (Sum.inr ⟨(i, j), s⟩ : Slot P) = 0 := by
    show VSPh.load P i j (P.Λ i j * qs i j) s = 0
    rw [h0]
    simp [VSPh.load]
  rw [hr, zero_pow hne]
  simp

lemma restr_stat (q : Policy P K) (π : State P K → ℝ) (hπ : IsStationary q π)
    (A : State P K → Prop) [DecidablePred A]
    (hA : ∀ z w, 0 < π z → Step q z w → (A w ↔ A z))
    (hm : 0 < ∑ x, (if A x then π x else 0)) :
    IsStationary q (fun z => if A z then π z / ∑ x, (if A x then π x else 0) else 0) := by
  refine ⟨fun z => ?_, ?_, fun f => ?_⟩
  · dsimp only
    split_ifs
    · exact div_nonneg (hπ.1 z) hm.le
    · exact le_refl 0
  · have e : ∀ z, (if A z then π z / ∑ x, (if A x then π x else 0) else 0) =
        (if A z then π z else 0) / ∑ x, (if A x then π x else 0) := fun z => by
      split_ifs <;> simp
    simp only [e]
    rw [← Finset.sum_div, div_self hm.ne']
  · set fA : State P K → ℝ := fun x => if A x then f x else 0 with hfA
    have hpt : ∀ z, (if A z then π z / ∑ x, (if A x then π x else 0) else 0) * gen q.1 f z =
        π z * gen q.1 fA z / ∑ x, (if A x then π x else 0) := by
      intro z
      rcases (hπ.1 z).eq_or_lt with h0 | h0
      · rw [← h0]
        split_ifs <;> simp
      · by_cases hAz : A z
        · rw [if_pos hAz, gen_congr q fA f z (by simp only [hfA, if_pos hAz])
            (fun w hw => by simp only [hfA, if_pos ((hA z w h0 hw).mpr hAz)])]
          ring
        · rw [if_neg hAz, gen_zero_of_const q fA z (fun w hw => by
            simp only [hfA, if_neg hAz, if_neg (fun h => hAz ((hA z w h0 hw).mp h))])]
          simp
    simp only [hpt]
    rw [← Finset.sum_div, hπ.2.2 fA, zero_div]

lemma averaging (π : State P K → ℝ) (hπ0 : ∀ z, 0 ≤ π z) (hπ1 : ∑ z, π z = 1)
    (R : State P K → ℝ) (B : ℝ) (hB : B ≤ ∑ z, π z * R z)
    {β : Type*} [DecidableEq β] (α : State P K → β) :
    ∃ z0, 0 < π z0 ∧
      B * (∑ x, if α x = α z0 then π x else 0) ≤ ∑ x, (if α x = α z0 then π x else 0) * R x := by
  by_contra hne
  push Not at hne
  have hfib : ∀ g : State P K → ℝ,
      ∑ b ∈ (univ : Finset (State P K)).image α, ∑ x, (if α x = b then g x else 0) = ∑ x, g x := by
    intro g
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem α (mem_univ x))]
  have hle : ∀ b ∈ (univ : Finset (State P K)).image α,
      ∑ x, (if α x = b then π x else 0) * R x ≤ B * ∑ x, (if α x = b then π x else 0) := by
    intro b _
    by_cases hex : ∃ x, α x = b ∧ 0 < π x
    · obtain ⟨x, rfl, hx⟩ := hex
      exact (hne x hx).le
    · push Not at hex
      have h0 : ∀ x, (if α x = b then π x else 0) = 0 := fun x => by
        split_ifs with h
        · exact le_antisymm (hex x h) (hπ0 x)
        · rfl
      simp only [h0, zero_mul, Finset.sum_const_zero, mul_zero, le_refl]
  obtain ⟨z1, hz1⟩ : ∃ z1, 0 < π z1 := by
    by_contra h
    push Not at h
    have : ∑ z, π z ≤ 0 := Finset.sum_nonpos fun z _ => h z
    linarith
  have hlt : ∑ b ∈ (univ : Finset (State P K)).image α, ∑ x, (if α x = b then π x else 0) * R x <
      ∑ b ∈ (univ : Finset (State P K)).image α, B * ∑ x, (if α x = b then π x else 0) :=
    Finset.sum_lt_sum hle ⟨α z1, Finset.mem_image_of_mem α (mem_univ z1), hne z1 hz1⟩
  rw [← Finset.mul_sum, hfib π, hπ1, mul_one] at hlt
  have : ∑ b ∈ (univ : Finset (State P K)).image α, ∑ x, (if α x = b then π x else 0) * R x =
      ∑ x, π x * R x := by
    rw [← hfib (fun x => π x * R x)]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  linarith

lemma class_bound [Nonempty P.L] (qs : P.L → P.L → ℝ) (hqs : ∀ i j, 0 ≤ qs i j ∧ qs i j ≤ 1)
    (hfb : ∀ i, ∑ j, P.Λ i j * qs i j = ∑ j, P.Λ j i * qs j i)
    [DecidableEq ((flowGraph P qs).ConnectedComponent → ℕ)]
    (Kc : (flowGraph P qs).ConnectedComponent → ℕ) (z0 : State P K) (hz0 : 0 < mcPis qs K z0)
    (hKc : ∀ c, vehiclesIn P qs c z0 = Kc c) (B : ℝ)
    (hpart : B * (∑ x, if (fun c => vehiclesIn P qs c x) = (fun c => vehiclesIn P qs c z0)
        then mcPis qs K x else 0) ≤
      ∑ x, (if (fun c => vehiclesIn P qs c x) = (fun c => vehiclesIn P qs c z0)
        then mcPis qs K x else 0) * mcRew (staticPolicy P K qs hqs) x) :
    ∑ c, Kc c = K ∧
      (∃ π : State P K → ℝ, IsStationary (staticPolicy P K qs hqs) π ∧ ConcentratedOn P qs Kc π) ∧
      ∀ π : State P K → ℝ, IsStationary (staticPolicy P K qs hqs) π → ConcentratedOn P qs Kc π →
        B ≤ reward (staticPolicy P K qs hqs) π := by
  classical
  have hst : IsStationary (staticPolicy P K qs hqs) (mcPis qs K) := VSPF.pf_stationary qs hqs hfb K
  have hnl : ∀ x : State P K, mcPis qs K x ≠ 0 →
      ∀ i j (s : P.Ph i j), ¬ live P qs i j → x.1 (Sum.inr ⟨(i, j), s⟩) = 0 := by
    intro x hx i j s hl
    refine wt_nonlive qs hqs x ?_ i j s hl
    intro h
    apply hx
    simp only [mcPis, h, zero_div]
  have hA0 : OnAllocation P qs Kc z0 := ⟨hnl z0 hz0.ne', hKc⟩
  have hiff : ∀ x, (if OnAllocation P qs Kc x then mcPis qs K x else 0) =
      (if (fun c => vehiclesIn P qs c x) = (fun c => vehiclesIn P qs c z0)
        then mcPis qs K x else 0) := by
    intro x
    by_cases hx : mcPis qs K x = 0
    · simp [hx]
    · by_cases hO : OnAllocation P qs Kc x
      · rw [if_pos hO, if_pos (funext fun c => (hO.2 c).trans (hKc c).symm)]
      · rw [if_neg hO, if_neg (fun h => hO ⟨hnl x hx, fun c => (congrFun h c).trans (hKc c)⟩)]
  have hm : 0 < ∑ x, (if OnAllocation P qs Kc x then mcPis qs K x else 0) := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun x => if OnAllocation P qs Kc x then mcPis qs K x else 0)
      (fun x _ => by split_ifs; exacts [hst.1 x, le_refl 0]) (mem_univ z0))
    rw [if_pos hA0]
    exact hz0
  have hstep : ∀ z w, 0 < mcPis qs K z → Step (staticPolicy P K qs hqs) z w →
      (OnAllocation P qs Kc w ↔ OnAllocation P qs Kc z) := by
    intro z w hz hs
    have hw := supp_closed _ _ hst z w hs hz
    have hv := alloc_step qs hqs z w (hnl z hz.ne') hs
    constructor
    · intro h
      exact ⟨hnl z hz.ne', fun c => (hv c).symm.trans (h.2 c)⟩
    · intro h
      exact ⟨hnl w hw.ne', fun c => (hv c).trans (h.2 c)⟩
  have hK := restr_stat _ (mcPis qs K) hst (OnAllocation P qs Kc) hstep hm
  have hcon : ConcentratedOn P qs Kc (fun z => if OnAllocation P qs Kc z then mcPis qs K z /
      ∑ x, (if OnAllocation P qs Kc x then mcPis qs K x else 0) else 0) := by
    intro z hz
    by_contra hO
    exact hz (if_neg hO)
  refine ⟨sum_alloc qs Kc z0 hA0, ⟨_, hK, hcon⟩, fun π hπ hπc => ?_⟩
  rw [stat_unique_class qs hqs hfb Kc π _ hπ hK hπc hcon, reward_eq]
  have e : ∀ x, (if OnAllocation P qs Kc x then mcPis qs K x /
        ∑ y, (if OnAllocation P qs Kc y then mcPis qs K y else 0) else 0) *
          mcRew (staticPolicy P K qs hqs) x =
      (if OnAllocation P qs Kc x then mcPis qs K x else 0) * mcRew (staticPolicy P K qs hqs) x /
        ∑ y, (if OnAllocation P qs Kc y then mcPis qs K y else 0) := fun x => by
    split_ifs <;> ring
  simp only [e]
  rw [← Finset.sum_div, le_div_iff₀ hm]
  simp only [hiff]
  exact hpart

end VSMulti

open VehShare.MultiNet in
theorem solution (P : Instance) [Nonempty P.L] (K : ℕ) (Δ : ℝ)
    (hΔ : (K : ℝ) ≤ Δ) (qs : P.L → P.L → ℝ) (hqs : IsOptimal2 P Δ qs) :
    (∀ (q : Policy P K) (π : State P K → ℝ), IsStationary q π → reward q π ≤ Rs P qs) ∧
    ∃ Kc : (flowGraph P qs).ConnectedComponent → ℕ, ∑ c, Kc c = K ∧
      (∃ π : State P K → ℝ,
        IsStationary (staticPolicy P K qs hqs.1.1) π ∧ ConcentratedOn P qs Kc π) ∧
      ∀ π : State P K → ℝ, IsStationary (staticPolicy P K qs hqs.1.1) π →
        ConcentratedOn P qs Kc π →
          (K : ℝ) / ((Fintype.card P.L : ℝ) + K - 1 + LamOverMu P) * Rs P qs ≤
              reward (staticPolicy P K qs hqs.1.1) π ∧
            (0 < Rs P qs →
              reward (staticPolicy P K qs hqs.1.1) π / Rs P qs ≤
                  reward (staticPolicy P K qs hqs.1.1) π / Ropt P K ∧
                (K : ℝ) / ((Fintype.card P.L : ℝ) + K - 1 + LamOverMu P) ≤
                  reward (staticPolicy P K qs hqs.1.1) π / Rs P qs) := by
  classical
  have hb := hqs.1.1
  have hfb := hqs.1.2.1
  have hN : 1 ≤ Fintype.card P.L := Fintype.card_pos
  have hW0 : 0 ≤ workload P qs := VSMain.workload_nonneg qs hb
  have hWL : workload P qs ≤ LamOverMu P := VSMain.workload_le qs hb
  have hRs : 0 ≤ Rs P qs := VSMain.Rs_nonneg Δ hΔ qs hqs
  have hπ0 : IsStationary (staticPolicy P K qs hb)
      (fun z => VSPF.wt qs z / VehicleSharePricing.Static.pfNormConst (VSPF.rho qs) VSAux.isR K) :=
    VSPF.pf_stationary qs hb hfb K
  have hWsum : ∑ p : (Σ p : P.L × P.L, P.Ph p.1 p.2), VSPF.rho qs (Sum.inr p) = 1 * workload P qs := by
    rw [one_mul, Fintype.sum_sigma, Fintype.sum_prod_type]
    unfold workload
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => VSPh.load_sum P i j _
  have hbusy : ∀ i, VehicleSharePricing.Static.pfBusyProb (VSPF.rho qs) VSAux.isR K (Sum.inl i) =
      VehShare.SeqBounds.Bseq (Fintype.card P.L) (workload P qs) K K := fun i =>
    VSAux.busy_eq_Bseq (VSPF.rho qs) 1 (workload P qs) (VSPF.rho_nonneg qs hb) one_pos
      (fun _ => rfl) hW0 hWsum i K
  have hrew0 : reward (staticPolicy P K qs hb)
      (fun z => VSPF.wt qs z / VehicleSharePricing.Static.pfNormConst (VSPF.rho qs) VSAux.isR K) =
      VehShare.SeqBounds.Bseq (Fintype.card P.L) (workload P qs) K K * Rs P qs := by
    rw [VSMain.reward_pf, Rs, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hbusy]
  have hprop1 : ∀ (q : Policy P K) (π : State P K → ℝ), IsStationary q π → reward q π ≤ Rs P qs :=
    fun q π hπ => VSProp1.prop1 Δ hΔ qs hqs q π hπ
  have hB0 : (K : ℝ) / ((Fintype.card P.L : ℝ) + K - 1 + LamOverMu P) * Rs P qs ≤
      ∑ z, VSMulti.mcPis qs K z * VSMulti.mcRew (staticPolicy P K qs hb) z := by
    show _ ≤ reward (staticPolicy P K qs hb)
      (fun z => VSPF.wt qs z / VehicleSharePricing.Static.pfNormConst (VSPF.rho qs) VSAux.isR K)
    rw [hrew0]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK
      simp [VSAux.Bseq_zero]
    · exact mul_le_mul_of_nonneg_right ((VSMain.Bseq_lower _ hN _ (hW0.trans hWL) K K hK hK).trans
        (VSAux.Bseq_anti _ hN _ _ hW0 hWL K K)) hRs
  obtain ⟨z0, hz0, hpart⟩ := VSMulti.averaging (VSMulti.mcPis qs K) hπ0.1 hπ0.2.1
    (VSMulti.mcRew (staticPolicy P K qs hb)) _ hB0 (fun z c => vehiclesIn P qs c z)
  obtain ⟨hsum, hex, hall⟩ := VSMulti.class_bound qs hb hfb (fun c => vehiclesIn P qs c z0) z0 hz0
    (fun c => rfl) _ hpart
  refine ⟨hprop1, fun c => vehiclesIn P qs c z0, hsum, hex, fun π hπ hcon =>
    ⟨hall π hπ hcon, fun hpos => ⟨?_, ?_⟩⟩⟩
  · have hset_bdd : BddAbove
        {x | ∃ (q : Policy P K) (π : State P K → ℝ), IsStationary q π ∧ x = reward q π} := by
      refine ⟨Rs P qs, fun x hx => ?_⟩
      obtain ⟨q, π', hπ', hx⟩ := hx
      rw [hx]
      exact hprop1 q π' hπ'
    have hle_opt : reward (staticPolicy P K qs hb) π ≤ Ropt P K := by
      unfold Ropt
      exact le_csSup hset_bdd ⟨_, π, hπ, rfl⟩
    have hopt_le : Ropt P K ≤ Rs P qs := by
      unfold Ropt
      refine csSup_le ⟨_, _, _, hπ0, rfl⟩ fun x hx => ?_
      obtain ⟨q, π', hπ', hx⟩ := hx
      rw [hx]
      exact hprop1 q π' hπ'
    have hNr : (1 : ℝ) ≤ Fintype.card P.L := by exact_mod_cast hN
    have hden : 0 ≤ (Fintype.card P.L : ℝ) + K - 1 + LamOverMu P := by
      have := Nat.cast_nonneg (α := ℝ) K
      linarith [hW0.trans hWL]
    have hR0 : 0 ≤ reward (staticPolicy P K qs hb) π :=
      (mul_nonneg (div_nonneg (Nat.cast_nonneg K) hden) hRs).trans (hall π hπ hcon)
    rcases hR0.eq_or_lt with h | h
    · rw [← h, zero_div, zero_div]
    · exact div_le_div_of_nonneg_left hR0 (h.trans_le hle_opt) hopt_le
  · rw [le_div_iff₀ hpos]
    exact hall π hπ hcon
