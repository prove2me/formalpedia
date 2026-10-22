-- Prove2me | solution 1 for UnknownProphet.NoSamples.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:24:57.761236+00:00
-- url     : https://prove2.me/submissions/b9bd3e92-6484-48ab-b9be-5c2b51c60f02

import Mathlib
import Definitions.Def_UnknownProphet_NoSamples_Model

namespace UnknownProphet.NoSamples.Eq4Aux

open Finset UnknownProphet.NoSamples

/-- Probability (given the values) that the record rule never stops. -/
noncomputable def noStop {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin n → ℝ) : ℝ :=
  ∏ j : Fin n, (1 - (hatRule q hq).r j ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)))

/-- Average of `noStop` over uniformly random ranks. -/
noncomputable def NS {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ σ : Equiv.Perm (Fin n), noStop q hq (fun i => ((σ i : ℕ) : ℝ))

/-! ### Order invariance -/

lemma pickMax_congr {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (x y : Fin n → ℝ) (hlt : ∀ a b, x a < x b ↔ y a < y b)
    (hle : ∀ a b, x a ≤ x b ↔ y a ≤ y b) :
    pickMaxProb (hatRule q hq) x = pickMaxProb (hatRule q hq) y := by
  simp only [pickMaxProb, stopProb, hatRule, Function.comp_apply, hlt, hle]

lemma noStop_congr {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (x y : Fin n → ℝ) (hlt : ∀ a b, x a < x b ↔ y a < y b) :
    noStop q hq x = noStop q hq y := by
  simp only [noStop, hatRule, Function.comp_apply, hlt]

/-! ### Prefix lemmas -/

lemma hq_init {n : ℕ} (q : Fin (n + 1) → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i : Fin n, (fun j : Fin n => q (Fin.castSucc j)) i ∈ Set.Icc (0 : ℝ) 1 :=
  fun i => hq _

section Prefix

variable {n : ℕ} (q : Fin (n + 1) → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)


lemma r_castSucc (x : Fin (n + 1) → ℝ) (j : Fin n) :
    (hatRule q hq).r (Fin.castSucc j) ![] (x ∘ Fin.castLE (Nat.succ_le_of_lt (Fin.castSucc j).isLt)) =
      (hatRule (fun j : Fin n => q (Fin.castSucc j)) (hq_init q hq)).r j ![]
        ((fun j : Fin n => x (Fin.castSucc j)) ∘ Fin.castLE (Nat.succ_le_of_lt j.isLt)) := by
  simp only [hatRule]
  rfl

lemma stopProb_castSucc (x : Fin (n + 1) → ℝ) (j : Fin n) :
    stopProb (hatRule q hq) ![] x (Fin.castSucc j) =
      stopProb (hatRule (fun j : Fin n => q (Fin.castSucc j)) (hq_init q hq)) ![]
        (fun j : Fin n => x (Fin.castSucc j)) j := by
  unfold stopProb
  rw [← Fin.map_castSuccEmb_Iio, Finset.prod_map]
  refine congrArg₂ (· * ·) ?_ (r_castSucc q hq x j)
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (fun t => 1 - t) (r_castSucc q hq x i)

lemma noStop_snoc (x : Fin (n + 1) → ℝ) :
    noStop q hq x = noStop (fun j : Fin n => q (Fin.castSucc j)) (hq_init q hq)
        (fun j : Fin n => x (Fin.castSucc j)) *
      (1 - (hatRule q hq).r (Fin.last n) ![]
        (x ∘ Fin.castLE (Nat.succ_le_of_lt (Fin.last n).isLt))) := by
  unfold noStop
  rw [Fin.prod_univ_castSucc]
  refine congrArg₂ (· * ·) ?_ rfl
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (fun t => 1 - t) (r_castSucc q hq x i)

lemma stopProb_last (x : Fin (n + 1) → ℝ) :
    stopProb (hatRule q hq) ![] x (Fin.last n) =
      noStop (fun j : Fin n => q (Fin.castSucc j)) (hq_init q hq)
        (fun j : Fin n => x (Fin.castSucc j)) *
      (hatRule q hq).r (Fin.last n) ![]
        (x ∘ Fin.castLE (Nat.succ_le_of_lt (Fin.last n).isLt)) := by
  unfold stopProb noStop
  congr 1
  have : Finset.Iio (Fin.last n) = (Finset.univ : Finset (Fin n)).map Fin.castSuccEmb := by
    ext i
    simp only [Finset.mem_Iio, Finset.mem_map, Finset.mem_univ, true_and, Fin.coe_castSuccEmb]
    constructor
    · intro h
      exact ⟨i.castPred (Fin.ne_last_of_lt h), Fin.castSucc_castPred _ _⟩
    · rintro ⟨j, rfl⟩
      exact Fin.castSucc_lt_last j
  rw [this, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Fin.coe_castSuccEmb]
  rw [r_castSucc]

lemma r_last (x : Fin (n + 1) → ℝ) (hx : Function.Injective x) :
    (hatRule q hq).r (Fin.last n) ![]
        (x ∘ Fin.castLE (Nat.succ_le_of_lt (Fin.last n).isLt)) =
      if ∀ l, x l ≤ x (Fin.last n) then q (Fin.last n) else 0 := by
  simp only [hatRule]
  have hcl : ∀ l : Fin (n + 1), Fin.castLE (Nat.succ_le_of_lt (Fin.last n).isLt) l = l := by
    intro l; ext; simp
  simp only [Function.comp_apply, hcl, Fin.val_last]
  congr 1
  apply propext
  constructor
  · intro h l
    by_cases hl : l = Fin.last n
    · rw [hl]
    · exact (h l hl).le
  · intro h l hl
    exact lt_of_le_of_ne (h l) (fun e => hl (hx e))

lemma pickMax_snoc_last (x : Fin (n + 1) → ℝ) (hx : Function.Injective x)
    (hmax : ∀ l, x l ≤ x (Fin.last n)) :
    pickMaxProb (hatRule q hq) x =
      noStop (fun j : Fin n => q (Fin.castSucc j)) (hq_init q hq)
        (fun j : Fin n => x (Fin.castSucc j)) * q (Fin.last n) := by
  unfold pickMaxProb
  rw [Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin n, (if ∀ l, x l ≤ x (Fin.castSucc j) then
      stopProb (hatRule q hq) ![] x (Fin.castSucc j) else 0) = 0 := by
    intro j
    rw [if_neg]
    intro h
    have h1 := h (Fin.last n)
    have h2 := hmax (Fin.castSucc j)
    have := hx (le_antisymm h2 h1)
    exact (Fin.castSucc_lt_last j).ne this
  simp only [h0, Finset.sum_const_zero, zero_add]
  rw [if_pos hmax, stopProb_last, r_last q hq x hx, if_pos hmax]

lemma pickMax_snoc_notlast (x : Fin (n + 1) → ℝ) (hx : Function.Injective x)
    (hmax : ¬ ∀ l, x l ≤ x (Fin.last n)) :
    pickMaxProb (hatRule q hq) x =
      pickMaxProb (hatRule (fun j : Fin n => q (Fin.castSucc j)) (hq_init q hq))
        (fun j : Fin n => x (Fin.castSucc j)) := by
  unfold pickMaxProb
  rw [Fin.sum_univ_castSucc, if_neg hmax, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [stopProb_castSucc]
  congr 1
  apply propext
  constructor
  · intro h l; exact h (Fin.castSucc l)
  · intro h l
    induction l using Fin.lastCases with
    | last =>
      push Not at hmax
      obtain ⟨l0, hl0⟩ := hmax
      induction l0 using Fin.lastCases with
      | last => exact absurd hl0 (lt_irrefl _)
      | cast l1 => exact le_trans hl0.le (h l1)
    | cast l => exact h l

end Prefix

/-! ### Decomposition of permutations of `Fin (n+1)` by the value at the last position -/

section Decomp

variable {n : ℕ}

def phiFun (m : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) : Fin (n + 1) → Fin (n + 1) :=
  Fin.lastCases m (fun j => m.succAbove (τ j))

lemma phiFun_last (m : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    phiFun m τ (Fin.last n) = m := by simp [phiFun]

lemma phiFun_castSucc (m : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    phiFun m τ (Fin.castSucc j) = m.succAbove (τ j) := by simp [phiFun]

lemma phiFun_inj (m : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) : Function.Injective (phiFun m τ) := by
  intro a b hab
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast b =>
      rw [phiFun_last, phiFun_castSucc] at hab
      exact absurd hab.symm (Fin.succAbove_ne m _)
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [phiFun_last, phiFun_castSucc] at hab
      exact absurd hab (Fin.succAbove_ne m _)
    | cast b =>
      rw [phiFun_castSucc, phiFun_castSucc] at hab
      rw [τ.injective (Fin.succAbove_right_injective hab)]

noncomputable def phi (m : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (phiFun m τ) (phiFun_inj m τ).bijective_of_finite

lemma phi_apply (m : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (a : Fin (n + 1)) :
    phi m τ a = phiFun m τ a := rfl

lemma phi_bij : Function.Bijective (fun p : Fin (n + 1) × Equiv.Perm (Fin n) => phi p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · rintro ⟨m, τ⟩ ⟨m', τ'⟩ h
    simp only at h
    have h1 : m = m' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n)) h
      simp only [phi_apply, phiFun_last] at this
      exact this
    subst h1
    have h2 : τ = τ' := by
      ext j
      have := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.castSucc j)) h
      simp only [phi_apply, phiFun_castSucc] at this
      rw [Fin.succAbove_right_injective this]
    rw [h2]
  · simp [Fintype.card_perm, Nat.factorial_succ]

lemma sum_perm_succ (f : Equiv.Perm (Fin (n + 1)) → ℝ) :
    ∑ σ, f σ = ∑ m : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), f (phi m τ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ phi_bij _ _ (fun p => rfl)).symm

lemma vals_phi_order (m : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    ∀ a b : Fin n,
      ((fun j : Fin n => (((phi m τ (Fin.castSucc j)) : ℕ) : ℝ)) a <
        (fun j : Fin n => (((phi m τ (Fin.castSucc j)) : ℕ) : ℝ)) b ↔
      ((τ a : ℕ) : ℝ) < ((τ b : ℕ) : ℝ)) ∧
      ((fun j : Fin n => (((phi m τ (Fin.castSucc j)) : ℕ) : ℝ)) a ≤
        (fun j : Fin n => (((phi m τ (Fin.castSucc j)) : ℕ) : ℝ)) b ↔
      ((τ a : ℕ) : ℝ) ≤ ((τ b : ℕ) : ℝ)) := by
  intro a b
  refine ⟨?_, ?_⟩ <;>
  simp [phi_apply, phiFun_castSucc, Nat.cast_lt, Nat.cast_le, Fin.val_fin_lt, Fin.val_fin_le,
    Fin.succAbove_lt_succAbove_iff, Fin.succAbove_le_succAbove_iff]

lemma phi_max_last_iff (m : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    (∀ l, (((phi m τ l) : ℕ) : ℝ) ≤ (((phi m τ (Fin.last n)) : ℕ) : ℝ)) ↔ m = Fin.last n := by
  constructor
  · intro h
    by_contra hm
    -- the value `last n` is attained at some position
    obtain ⟨l, hl⟩ := (phi m τ).surjective (Fin.last n)
    have := h l
    rw [hl, phi_apply, phiFun_last, Nat.cast_le] at this
    exact hm (le_antisymm (Fin.le_last m) this)
  · intro hm l
    rw [phi_apply _ τ (Fin.last n), phiFun_last, Nat.cast_le, hm]
    exact Fin.le_last _

end Decomp

/-! ### The recursions -/

lemma vals_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun i => ((σ i : ℕ) : ℝ)) := by
  intro a b h
  simp only [Nat.cast_inj] at h
  exact σ.injective (Fin.ext h)

lemma recursion {n : ℕ} (q : Fin (n + 1) → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) :
    recordRuleSuccess q hq =
      (n * recordRuleSuccess (fun j : Fin n => q (Fin.castSucc j)) (hq_init q hq) +
        NS (fun j : Fin n => q (Fin.castSucc j)) (hq_init q hq) * q (Fin.last n)) / (n + 1) ∧
    NS q hq = NS (fun j : Fin n => q (Fin.castSucc j)) (hq_init q hq) *
      (1 - q (Fin.last n) / (n + 1)) := by
  set q' := fun j : Fin n => q (Fin.castSucc j)
  set hq' := hq_init q hq
  set G := ∑ τ : Equiv.Perm (Fin n), pickMaxProb (hatRule q' hq') (fun i => ((τ i : ℕ) : ℝ))
  set H := ∑ τ : Equiv.Perm (Fin n), noStop q' hq' (fun i => ((τ i : ℕ) : ℝ))
  have hfact : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hnf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  -- per (m, τ) evaluations
  have hpick : ∀ (m : Fin (n + 1)) (τ : Equiv.Perm (Fin n)),
      pickMaxProb (hatRule q hq) (fun i => ((phi m τ i : ℕ) : ℝ)) =
        if m = Fin.last n then noStop q' hq' (fun i => ((τ i : ℕ) : ℝ)) * q (Fin.last n)
        else pickMaxProb (hatRule q' hq') (fun i => ((τ i : ℕ) : ℝ)) := by
    intro m τ
    have hord := vals_phi_order m τ
    split_ifs with hm
    · rw [pickMax_snoc_last q hq _ (vals_inj _) ((phi_max_last_iff m τ).mpr hm)]
      congr 1
      exact noStop_congr q' hq' _ _ (fun a b => (hord a b).1)
    · rw [pickMax_snoc_notlast q hq _ (vals_inj _) (fun h => hm ((phi_max_last_iff m τ).mp h))]
      exact pickMax_congr q' hq' _ _ (fun a b => (hord a b).1) (fun a b => (hord a b).2)
  have hns : ∀ (m : Fin (n + 1)) (τ : Equiv.Perm (Fin n)),
      noStop q hq (fun i => ((phi m τ i : ℕ) : ℝ)) =
        noStop q' hq' (fun i => ((τ i : ℕ) : ℝ)) *
          (1 - if m = Fin.last n then q (Fin.last n) else 0) := by
    intro m τ
    have hord := vals_phi_order m τ
    rw [noStop_snoc q hq, r_last q hq _ (vals_inj _)]
    congr 1
    · exact noStop_congr q' hq' _ _ (fun a b => (hord a b).1)
    · congr 1
      by_cases hm : m = Fin.last n
      · rw [if_pos ((phi_max_last_iff m τ).mpr hm), if_pos hm]
      · rw [if_neg (fun h => hm ((phi_max_last_iff m τ).mp h)), if_neg hm]
  constructor
  · unfold recordRuleSuccess
    rw [sum_perm_succ]
    simp_rw [hpick]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_ne_last, if_false, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_mul]
    unfold NS
    rw [hfact]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · unfold NS
    rw [sum_perm_succ]
    simp_rw [hns]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_ne_last, if_false, if_true, sub_zero, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
    rw [hfact]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring


/-! ### Closed form -/

lemma closed_form (Q : ℕ → ℝ) : ∀ (n : ℕ) (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1),
    (∀ j, q j = Q j.val) →
      NS q hq = ∏ k ∈ range n, (1 - Q k / (k + 1)) ∧
      (n : ℝ) * recordRuleSuccess q hq =
        ∑ k ∈ range n, Q k * ∏ j ∈ range k, (1 - Q j / (j + 1)) := by
  intro n
  induction n with
  | zero =>
    intro q hq _
    constructor
    · simp [NS, noStop]
    · simp
  | succ n ih =>
    intro q hq hqQ
    obtain ⟨hr1, hr2⟩ := recursion q hq
    have hq' : ∀ j : Fin n, (fun j : Fin n => q (Fin.castSucc j)) j = Q j.val := by
      intro j; simp [hqQ]
    obtain ⟨i1, i2⟩ := ih _ (hq_init q hq) hq'
    have hlast : q (Fin.last n) = Q n := by rw [hqQ]; simp
    constructor
    · rw [hr2, i1, hlast, Finset.prod_range_succ]
    · rw [hr1, hlast, Finset.sum_range_succ, ← i2, i1]
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp

/-! ### The dynamic-programming bound -/

lemma harmonic_le (k N : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∑ j ∈ Ico k N, (1 : ℝ) / j ≤ 1 / k + Real.log ((N : ℝ) / k) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rcases Nat.eq_or_lt_of_le hkN with h | h
  · subst h; simp
  -- prove for N ≥ k+1 the stronger bound with N-1
  have key : ∀ M : ℕ, k + 1 ≤ M →
      ∑ j ∈ Ico k M, (1 : ℝ) / j ≤ 1 / k + Real.log (((M : ℝ) - 1) / k) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.Ico_self, Finset.sum_empty]
      push_cast
      simp
    | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hM1 : (k : ℝ) + 1 ≤ M := by exact_mod_cast hM
      have hpos : (0 : ℝ) < (M : ℝ) - 1 := by linarith
      have hstep : (1 : ℝ) / M ≤ Real.log ((M : ℝ) / ((M : ℝ) - 1)) := by
        have hM0 : (M : ℝ) ≠ 0 := by linarith
        have := Real.one_sub_inv_le_log_of_pos (x := (M : ℝ) / ((M : ℝ) - 1))
          (div_pos (by linarith) hpos)
        have e : 1 - ((M : ℝ) / ((M : ℝ) - 1))⁻¹ = 1 / M := by
          rw [inv_div]; field_simp; ring
        linarith
      have hsplit : Real.log ((((M + 1 : ℕ) : ℝ) - 1) / k) =
          Real.log (((M : ℝ) - 1) / k) + Real.log ((M : ℝ) / ((M : ℝ) - 1)) := by
        have hk0 : (0 : ℝ) < k := by linarith
        rw [← Real.log_mul (div_pos hpos hk0).ne' (div_pos (by linarith) hpos).ne']
        congr 1
        push_cast
        field_simp
        ring
      rw [hsplit]
      linarith
  have h1 := key N h
  have hN : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : k + 1 ≤ N := h
    have : (k : ℝ) + 1 ≤ N := by exact_mod_cast this
    linarith
  have h2 : Real.log (((N : ℝ) - 1) / k) ≤ Real.log ((N : ℝ) / k) := by
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

lemma klog_le (k N : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * Real.log ((N : ℝ) / k) ≤ N / Real.exp 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set t : ℝ := (N : ℝ) / k
  have ht : 0 < t := by positivity
  have h1 := Real.log_le_sub_one_of_pos (x := t / Real.exp 1) (by positivity)
  rw [Real.log_div ht.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
  have h2 : Real.log t ≤ t / Real.exp 1 := by linarith
  have h3 : (k : ℝ) * Real.log t ≤ k * (t / Real.exp 1) := mul_le_mul_of_nonneg_left h2 hkR.le
  have h4 : (k : ℝ) * (t / Real.exp 1) = N / Real.exp 1 := by
    simp only [t]; field_simp
  linarith

lemma dp_bound (Q : ℕ → ℝ) (hQ : ∀ k, 0 ≤ Q k ∧ Q k ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ range N, Q k * ∏ j ∈ range k, (1 - Q j / (j + 1)) ≤ 1 + N / Real.exp 1 := by
  set M : ℝ := 1 + N / Real.exp 1 with hMdef
  set T : ℕ → ℝ := fun k => ∏ j ∈ range k, (1 - Q j / (j + 1)) with hTdef
  set ψ : ℕ → ℝ := fun k => (k : ℝ) * ∑ j ∈ Ico k N, (1 : ℝ) / j with hψdef
  set Φ : ℕ → ℝ := fun k => if M ≤ (k : ℝ) + 1 then ψ k else M with hΦdef
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM1 : 1 < M := by
    have : 0 < (N : ℝ) / Real.exp 1 := by positivity
    linarith
  have hT0 : ∀ k, 0 ≤ T k := by
    intro k
    apply Finset.prod_nonneg
    intro j _
    have := hQ j
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have : (0 : ℝ) ≤ j := by positivity
                                          linarith
    have : Q j / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  have hTs : ∀ k, T (k + 1) = T k * (1 - Q k / (k + 1)) := by
    intro k; simp only [T]; rw [Finset.prod_range_succ]
  have hψbd : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ ψ k ∧ ψ k ≤ M := by
    intro k hk hkN
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    constructor
    · simp only [ψ]
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun j _ => by positivity)
    · have h1 := harmonic_le k N hk hkN
      have h2 := klog_le k N hk
      simp only [ψ]
      have : (k : ℝ) * ∑ j ∈ Ico k N, (1 : ℝ) / j ≤ k * (1 / k + Real.log ((N : ℝ) / k)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have e : (k : ℝ) * (1 / k + Real.log ((N : ℝ) / k)) = 1 + k * Real.log ((N : ℝ) / k) := by
        field_simp
      linarith
  have hψN : ψ N = 0 := by simp [ψ]
  have hψrec : ∀ k, 1 ≤ k → k < N → ψ k = 1 + (k / (k + 1)) * ψ (k + 1) := by
    intro k hk hkN
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    simp only [ψ]
    rw [Finset.sum_eq_sum_Ico_succ_bot hkN]
    push_cast
    field_simp
  have hΦ0 : ∀ k, k ≤ N → 0 ≤ Φ k ∧ Φ k ≤ M := by
    intro k hkN
    simp only [Φ]
    split_ifs with h
    · have hk1 : 1 ≤ k := by
        by_contra hc
        push Not at hc
        have : k = 0 := by omega
        subst this
        simp at h; linarith
      exact hψbd k hk1 hkN
    · exact ⟨by linarith, le_refl _⟩
  -- downward induction
  have main : ∀ r, r ≤ N → ∑ j ∈ Ico (N - r) N, Q j * T j ≤ T (N - r) * Φ (N - r) := by
    intro r
    induction r with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Finset.Ico_self, Finset.sum_empty]
      exact mul_nonneg (hT0 N) (hΦ0 N le_rfl).1
    | succ r ih =>
      intro hr
      have ih' := ih (by omega)
      set k := N - (r + 1) with hk
      have hk1 : N - r = k + 1 := by omega
      rw [hk1] at ih'
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : k < N)]
      have hQk := hQ k
      have hkR0 : (0 : ℝ) ≤ k := by positivity
      set P := Φ (k + 1)
      have hP := hΦ0 (k + 1) (by omega)
      have step : Q k * T k + ∑ j ∈ Ico (k + 1) N, Q j * T j ≤
          T k * (Q k + (1 - Q k / (k + 1)) * P) := by
        have := ih'
        rw [hTs k] at this
        have e : T k * (Q k + (1 - Q k / (k + 1)) * P) = Q k * T k + T k * (1 - Q k / (k + 1)) * P := by
          ring
        linarith
      refine le_trans step (mul_le_mul_of_nonneg_left ?_ (hT0 k))
      -- the one-step inequality
      have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      have hlin : Q k + (1 - Q k / (k + 1)) * P = P + Q k * (1 - P / (k + 1)) := by
        field_simp; ring
      rw [hlin]
      simp only [Φ]
      split_ifs with hMk
      · -- regime `M ≤ k+1`
        have hk1 : 1 ≤ k := by
          by_contra hc
          push Not at hc
          have : k = 0 := by omega
          have hk0 : (k : ℝ) = 0 := by exact_mod_cast this
          rw [hk0] at hMk; linarith
        have hPψ : P = ψ (k + 1) := by
          simp only [P, Φ]
          rw [if_pos (by push_cast; linarith)]
        have hPle : P ≤ (k : ℝ) + 1 := le_trans hP.2 hMk
        rw [hψrec k hk1 (by omega), ← hPψ]
        have : (P / ((k : ℝ) + 1)) ≤ 1 := by rw [div_le_one hk1R]; exact hPle
        have e : 1 + (k : ℝ) / (k + 1) * P = P + 1 * (1 - P / (k + 1)) := by
          field_simp; ring
        rw [e]
        have : Q k * (1 - P / (k + 1)) ≤ 1 * (1 - P / (k + 1)) :=
          mul_le_mul_of_nonneg_right hQk.2 (by linarith)
        linarith
      · -- regime `k+1 < M`
        push Not at hMk
        by_cases hPk : P ≤ (k : ℝ) + 1
        · have h1 : Q k * (1 - P / (k + 1)) ≤ 1 - P / (k + 1) := by
            have : 0 ≤ 1 - P / (k + 1) := by
              rw [sub_nonneg, div_le_one hk1R]; exact hPk
            nlinarith [hQk.2]
          have h2 : P + (1 - P / (k + 1)) ≤ M := by
            have e : P + (1 - P / (k + 1)) = 1 + P * (k / (k + 1)) := by field_simp; ring
            rw [e]
            have hk' : (k : ℝ) / (k + 1) ≤ 1 := by rw [div_le_one hk1R]; linarith
            have : P * (k / (k + 1)) ≤ M * (k / (k + 1)) :=
              mul_le_mul_of_nonneg_right hP.2 (by positivity)
            have : M * ((k : ℝ) / (k + 1)) = M - M / (k + 1) := by field_simp; ring
            have : 1 ≤ M / ((k : ℝ) + 1) := by rw [le_div_iff₀ hk1R]; linarith
            linarith
          linarith
        · push Not at hPk
          have : Q k * (1 - P / (k + 1)) ≤ 0 := by
            apply mul_nonpos_of_nonneg_of_nonpos hQk.1
            rw [sub_nonpos, le_div_iff₀ hk1R]; linarith
          linarith [hP.2]
  have hT00 : T 0 = 1 := by simp [T]
  have hΦ00 : Φ 0 = M := by
    simp only [Φ]; rw [if_neg]; push_cast; linarith
  have := main N le_rfl
  rw [Nat.sub_self, hT00, hΦ00, one_mul, ← Finset.range_eq_Ico] at this
  exact this

end UnknownProphet.NoSamples.Eq4Aux

open UnknownProphet.NoSamples UnknownProphet.NoSamples.Eq4Aux in
theorem solution (δ : ℝ) (hδ : 0 < δ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1),
        recordRuleSuccess q hq ≤ Real.exp (-1) + δ := by
  refine ⟨⌈1 / δ⌉₊ + 1, fun n hn q hq => ?_⟩
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  set Q : ℕ → ℝ := fun k => if h : k < n then q ⟨k, h⟩ else 0
  have hQ : ∀ k, 0 ≤ Q k ∧ Q k ≤ 1 := by
    intro k
    simp only [Q]
    split_ifs with h
    · exact ⟨(hq _).1, (hq _).2⟩
    · exact ⟨le_refl 0, zero_le_one⟩
  have hqQ : ∀ j : Fin n, q j = Q j.val := by
    intro j; simp only [Q, dif_pos j.isLt]
  obtain ⟨_, h2⟩ := closed_form Q n q hq hqQ
  have hdp := dp_bound Q hQ n hn1
  rw [← h2] at hdp
  have hRS : recordRuleSuccess q hq ≤ 1 / n + 1 / Real.exp 1 := by
    have e : 1 / (n : ℝ) + 1 / Real.exp 1 = (1 + n / Real.exp 1) / n := by
      field_simp
    rw [e, le_div_iff₀ hnpos]
    linarith
  have hexp : Real.exp (-1) = 1 / Real.exp 1 := by
    rw [Real.exp_neg, one_div]
  have hnδ : 1 / (n : ℝ) ≤ δ := by
    have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    rw [div_le_iff₀ hnpos]
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  rw [hexp]
  linarith
