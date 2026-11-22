-- Prove2me | solution 1 for SampleDrivenOS.Limit.sdclpValue_le_alphaStar
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:03:38.170803+00:00
-- url     : https://prove2.me/submissions/d4e63ba4-33e3-4887-8c27-ffb4dd3a10be

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology SampleDrivenOS.Limit SampleDrivenOS.Structure

namespace SampleDrivenOS.Limit.UpperBoundProof

open Set

/-! ### Part 1: Combinatorial and Poisson series identities -/

lemma nbTerm_eq_binom_tail (k ℓ : ℕ) (hℓ : 1 ≤ ℓ) (t : ℝ) :
    nbTerm k ℓ t =
      ∑ m ∈ Finset.Icc ℓ k, (k.choose m : ℝ) * t ^ m * (1 - t) ^ (k - m) := by
  induction k with
  | zero =>
    have h1 : Finset.Icc ℓ 0 = ∅ := Finset.Icc_eq_empty (by omega)
    simp [nbTerm, h1]
  | succ k ih =>
    by_cases hlk : ℓ ≤ k + 1
    · have hIcc : Finset.Icc ℓ (k + 1) = insert (k + 1) (Finset.Icc ℓ k) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : k + 1 ∉ Finset.Icc ℓ k := by
        simp only [Finset.mem_Icc]
        omega
      have hlhs : nbTerm (k + 1) ℓ t =
          nbTerm k ℓ t + (k.choose (ℓ - 1) : ℝ) * (1 - t) ^ (k + 1 - ℓ) * t ^ ℓ := by
        unfold nbTerm
        rw [hIcc, Finset.sum_insert hnotmem, add_comm]
        simp
      rw [hlhs, ih]
      have hsplit :
          ∑ m ∈ Finset.Icc ℓ (k + 1), ((k + 1).choose m : ℝ) * t ^ m * (1 - t) ^ (k + 1 - m) =
            (∑ m ∈ Finset.Icc ℓ (k + 1), (k.choose m : ℝ) * t ^ m * (1 - t) ^ (k + 1 - m)) +
            (∑ m ∈ Finset.Icc ℓ (k + 1), (k.choose (m - 1) : ℝ) * t ^ m * (1 - t) ^ (k + 1 - m)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm1 : 1 ≤ m := le_trans hℓ (Finset.mem_Icc.mp hm).1
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        rw [Nat.choose_succ_succ, Nat.succ_sub_one]
        push_cast
        ring
      rw [hsplit]
      have hsum1 :
          ∑ m ∈ Finset.Icc ℓ (k + 1), (k.choose m : ℝ) * t ^ m * (1 - t) ^ (k + 1 - m) =
            (1 - t) * ∑ m ∈ Finset.Icc ℓ k, (k.choose m : ℝ) * t ^ m * (1 - t) ^ (k - m) := by
        rw [hIcc, Finset.sum_insert hnotmem]
        have hzero : k.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k)
        rw [hzero]
        simp only [Nat.cast_zero, zero_mul, zero_add, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hmk : m ≤ k := (Finset.mem_Icc.mp hm).2
        have hsub : k + 1 - m = (k - m) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      have hsum2 :
          ∑ m ∈ Finset.Icc ℓ (k + 1), (k.choose (m - 1) : ℝ) * t ^ m * (1 - t) ^ (k + 1 - m) =
            t * ((k.choose (ℓ - 1) : ℝ) * t ^ (ℓ - 1) * (1 - t) ^ (k - (ℓ - 1)) +
              ∑ r ∈ Finset.Icc ℓ k, (k.choose r : ℝ) * t ^ r * (1 - t) ^ (k - r)) := by
        have hbij :
            ∑ m ∈ Finset.Icc ℓ (k + 1), (k.choose (m - 1) : ℝ) * t ^ m * (1 - t) ^ (k + 1 - m) =
              ∑ r ∈ Finset.Icc (ℓ - 1) k, (k.choose r : ℝ) * t ^ (r + 1) * (1 - t) ^ (k - r) := by
          refine Finset.sum_nbij (fun m => m - 1) ?_ ?_ ?_ ?_
          · intro m hm
            simp only [Finset.mem_Icc] at hm ⊢
            omega
          · intro m₁ hm₁ m₂ hm₂ h
            simp only [Finset.mem_coe, Finset.mem_Icc] at hm₁ hm₂
            dsimp only at h
            omega
          · intro r hr
            simp only [Finset.mem_coe, Finset.mem_Icc] at hr
            refine ⟨r + 1, ?_, by simp⟩
            simp only [Finset.mem_coe, Finset.mem_Icc]
            omega
          · intro m hm
            simp only [Finset.mem_Icc] at hm
            have h1 : m - 1 + 1 = m := by omega
            have h2 : k - (m - 1) = k + 1 - m := by omega
            rw [h1, h2]
        rw [hbij]
        have hIcc2 : Finset.Icc (ℓ - 1) k = insert (ℓ - 1) (Finset.Icc ℓ k) := by
          ext r
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hnotmem2 : ℓ - 1 ∉ Finset.Icc ℓ k := by
          simp only [Finset.mem_Icc]
          omega
        rw [hIcc2, Finset.sum_insert hnotmem2, mul_add, Finset.mul_sum]
        congr 1
        · rw [pow_succ]; ring
        · refine Finset.sum_congr rfl fun r _ => ?_
          rw [pow_succ]; ring
      rw [hsum1, hsum2]
      have hexp : k - (ℓ - 1) = k + 1 - ℓ := by omega
      have hpow : t * t ^ (ℓ - 1) = t ^ ℓ := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hexp]
      calc
        (∑ m ∈ Finset.Icc ℓ k, (k.choose m : ℝ) * t ^ m * (1 - t) ^ (k - m)) +
            (k.choose (ℓ - 1) : ℝ) * (1 - t) ^ (k + 1 - ℓ) * t ^ ℓ
          = (∑ m ∈ Finset.Icc ℓ k, (k.choose m : ℝ) * t ^ m * (1 - t) ^ (k - m)) +
            (k.choose (ℓ - 1) : ℝ) * (1 - t) ^ (k + 1 - ℓ) * (t * t ^ (ℓ - 1)) := by rw [hpow]
        _ = (1 - t) * (∑ m ∈ Finset.Icc ℓ k, (k.choose m : ℝ) * t ^ m * (1 - t) ^ (k - m)) +
            t * ((k.choose (ℓ - 1) : ℝ) * t ^ (ℓ - 1) * (1 - t) ^ (k + 1 - ℓ) +
              ∑ r ∈ Finset.Icc ℓ k, (k.choose r : ℝ) * t ^ r * (1 - t) ^ (k - r)) := by ring
    · have h1 : Finset.Icc ℓ (k + 1) = ∅ := Finset.Icc_eq_empty (by omega)
      simp [nbTerm, h1]

lemma nbTerm_nonneg (k ℓ : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ nbTerm k ℓ t := by
  unfold nbTerm
  refine Finset.sum_nonneg fun j _ => ?_
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr ht.2) _))
    (pow_nonneg ht.1 _)

lemma nbTerm_le_one (k ℓ : ℕ) (hℓ : 1 ≤ ℓ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    nbTerm k ℓ t ≤ 1 := by
  rw [nbTerm_eq_binom_tail k ℓ hℓ t]
  have hsub : Finset.Icc ℓ k ⊆ Finset.range (k + 1) := by
    intro m hm
    simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢
    omega
  calc
    ∑ m ∈ Finset.Icc ℓ k, (k.choose m : ℝ) * t ^ m * (1 - t) ^ (k - m)
      ≤ ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * t ^ m * (1 - t) ^ (k - m) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => ?_
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
          (pow_nonneg (sub_nonneg.mpr ht.2) _)
    _ = ∑ m ∈ Finset.range (k + 1), t ^ m * (1 - t) ^ (k - m) * (k.choose m : ℝ) := by
        refine Finset.sum_congr rfl fun m _ => by ring
    _ = (t + (1 - t)) ^ k := (add_pow t (1 - t) k).symm
    _ = 1 := by ring_nf

lemma hasSum_real_exp (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

lemma ennreal_tsum_exp (x : ℝ) (hx : 0 ≤ x) :
    ∑' n : ℕ, ENNReal.ofReal (x ^ n / (n.factorial : ℝ)) = ENNReal.ofReal (Real.exp x) := by
  have hnn : ∀ n : ℕ, 0 ≤ x ^ n / (n.factorial : ℝ) := fun n =>
    div_nonneg (pow_nonneg hx n) (Nat.cast_nonneg _)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hasSum_real_exp x).summable, (hasSum_real_exp x).tsum_eq]

lemma ennreal_tsum_ite_le (ℓ : ℕ) (g : ℕ → ENNReal) :
    (∑' m : ℕ, if ℓ ≤ m then g m else 0) = ∑' m : ℕ, g (m + ℓ) := by
  induction ℓ generalizing g with
  | zero => simp
  | succ ℓ ih =>
    rw [tsum_eq_zero_add' ENNReal.summable]
    have h0 : ¬ (ℓ + 1 ≤ 0) := by omega
    simp only [h0, ↓reduceIte, zero_add, Nat.add_le_add_iff_right]
    rw [ih (fun m => g (m + 1))]
    refine tsum_congr fun m => by rw [Nat.add_assoc]

noncomputable def poissonTail (x : ℝ) (ℓ : ℕ) : ENNReal :=
  ∑' m : ℕ, ENNReal.ofReal (Real.exp (-x) * x ^ (m + ℓ) / ((m + ℓ).factorial : ℝ))

lemma tsum_poisson_nbTerm (lam t : ℝ) (hlam : 0 ≤ lam) (ht : t ∈ Icc (0 : ℝ) 1)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∑' k : ℕ, ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * nbTerm k ℓ t) =
      poissonTail (lam * t) ℓ := by
  have hstep1 :
      ∀ k : ℕ,
        ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * nbTerm k ℓ t) =
          ∑' m : ℕ, if ℓ ≤ m then
            (if m ≤ k then
              ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) *
                ((k.choose m : ℝ) * t ^ m * (1 - t) ^ (k - m)))
            else 0)
          else 0 := by
    intro k
    rw [nbTerm_eq_binom_tail k ℓ hℓ t, Finset.mul_sum]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · symm
      rw [tsum_eq_sum (s := Finset.Icc ℓ k)]
      · refine Finset.sum_congr rfl fun m hm => ?_
        simp only [Finset.mem_Icc] at hm
        simp [hm.1, hm.2]
      · intro m hm
        simp only [Finset.mem_Icc, not_and_or, not_le] at hm
        rcases hm with h | h
        · simp [not_le.mpr h]
        · by_cases hlm : ℓ ≤ m <;> simp [hlm, not_le.mpr h]
    · intro m _
      exact mul_nonneg
        (div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hlam _)) (Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
          (pow_nonneg (sub_nonneg.mpr ht.2) _))
  simp_rw [hstep1]
  rw [ENNReal.tsum_comm]
  have hpull :
      ∀ m : ℕ,
        (∑' k : ℕ, if ℓ ≤ m then
          (if m ≤ k then
            ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) *
              ((k.choose m : ℝ) * t ^ m * (1 - t) ^ (k - m)))
          else 0)
        else 0) =
        if ℓ ≤ m then
          ∑' k : ℕ, if m ≤ k then
            ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) *
              ((k.choose m : ℝ) * t ^ m * (1 - t) ^ (k - m)))
          else 0
        else 0 := by
    intro m
    by_cases hlm : ℓ ≤ m <;> simp [hlm]
  simp_rw [hpull]
  rw [ennreal_tsum_ite_le ℓ]
  unfold poissonTail
  refine tsum_congr fun m => ?_
  rw [ennreal_tsum_ite_le (m + ℓ)]
  set n := m + ℓ
  have hterm :
      ∀ r : ℕ,
        ENNReal.ofReal (Real.exp (-lam) * lam ^ (r + n) / ((r + n).factorial : ℝ) *
          (((r + n).choose n : ℝ) * t ^ n * (1 - t) ^ (r + n - n))) =
        ENNReal.ofReal (Real.exp (-lam) * (lam * t) ^ n / (n.factorial : ℝ)) *
          ENNReal.ofReal ((lam * (1 - t)) ^ r / (r.factorial : ℝ)) := by
    intro r
    have hnn1 : 0 ≤ Real.exp (-lam) * (lam * t) ^ n / (n.factorial : ℝ) :=
      div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (mul_nonneg hlam ht.1) _))
        (Nat.cast_nonneg _)
    rw [← ENNReal.ofReal_mul hnn1]
    congr 1
    have hchoose : ((r + n).choose n : ℝ) * (n.factorial : ℝ) * (r.factorial : ℝ) =
        ((r + n).factorial : ℝ) := by
      have hnat : (r + n).choose n * n.factorial * r.factorial = (r + n).factorial := by
        have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left n r)
        simpa [Nat.add_sub_cancel] using this
      exact_mod_cast hnat
    have hnfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hrfac : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
    have hchn : ((r + n).choose n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_left n r)).ne'
    simp only [Nat.add_sub_cancel]
    calc
      Real.exp (-lam) * lam ^ (r + n) / ((r + n).factorial : ℝ) *
          (((r + n).choose n : ℝ) * t ^ n * (1 - t) ^ r)
        = Real.exp (-lam) * (lam ^ r * lam ^ n) * ((r + n).choose n : ℝ) * t ^ n * (1 - t) ^ r /
            (((r + n).choose n : ℝ) * (n.factorial : ℝ) * (r.factorial : ℝ)) := by
          rw [hchoose, pow_add]; ring
      _ = Real.exp (-lam) * (lam * t) ^ n / (n.factorial : ℝ) *
            ((lam * (1 - t)) ^ r / (r.factorial : ℝ)) := by
          rw [mul_pow, mul_pow]
          field_simp [hchn, hnfac, hrfac]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ennreal_tsum_exp (lam * (1 - t)) (mul_nonneg hlam (sub_nonneg.mpr ht.2))]
  rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (mul_nonneg hlam ht.1) _)) (Nat.cast_nonneg _))]
  congr 1
  have hexp : Real.exp (-lam) * Real.exp (lam * (1 - t)) = Real.exp (-(lam * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-lam) * (lam * t) ^ n / (n.factorial : ℝ) * Real.exp (lam * (1 - t))
      = (Real.exp (-lam) * Real.exp (lam * (1 - t))) * (lam * t) ^ n / (n.factorial : ℝ) := by ring
    _ = Real.exp (-(lam * t)) * (lam * t) ^ n / (n.factorial : ℝ) := by rw [hexp]

lemma poissonTail_le_one (x : ℝ) (hx : 0 ≤ x) (ℓ : ℕ) :
    poissonTail x ℓ ≤ 1 := by
  unfold poissonTail
  rw [← ennreal_tsum_ite_le ℓ (fun n => ENNReal.ofReal (Real.exp (-x) * x ^ n / (n.factorial : ℝ)))]
  calc
    (∑' n : ℕ, if ℓ ≤ n then ENNReal.ofReal (Real.exp (-x) * x ^ n / (n.factorial : ℝ)) else 0)
      ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (-x) * x ^ n / (n.factorial : ℝ)) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        split_ifs <;> simp
    _ = ∑' n : ℕ, ENNReal.ofReal (Real.exp (-x)) * ENNReal.ofReal (x ^ n / (n.factorial : ℝ)) := by
        refine tsum_congr fun n => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), mul_div_assoc]
    _ = ENNReal.ofReal (Real.exp (-x)) * ENNReal.ofReal (Real.exp x) := by
        rw [ENNReal.tsum_mul_left, ennreal_tsum_exp x hx]
    _ = 1 := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, neg_add_cancel, Real.exp_zero,
          ENNReal.ofReal_one]

lemma tsum_poissonTail_succ (x : ℝ) (hx : 0 ≤ x) :
    ∑' r : ℕ, poissonTail x (r + 1) = ENNReal.ofReal x := by
  unfold poissonTail
  have hrew : ∀ r : ℕ,
      (∑' m : ℕ, ENNReal.ofReal (Real.exp (-x) * x ^ (m + (r + 1)) / ((m + (r + 1)).factorial : ℝ))) =
        ∑' n : ℕ, if r + 1 ≤ n then ENNReal.ofReal (Real.exp (-x) * x ^ n / (n.factorial : ℝ)) else 0 :=
    fun r => (ennreal_tsum_ite_le (r + 1)
      (fun n => ENNReal.ofReal (Real.exp (-x) * x ^ n / (n.factorial : ℝ)))).symm
  simp_rw [hrew]
  rw [ENNReal.tsum_comm]
  have hinner : ∀ n : ℕ,
      (∑' r : ℕ, if r + 1 ≤ n then ENNReal.ofReal (Real.exp (-x) * x ^ n / (n.factorial : ℝ)) else 0) =
        (n : ENNReal) * ENNReal.ofReal (Real.exp (-x) * x ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [tsum_eq_sum (s := Finset.range n)]
    · rw [Finset.sum_congr rfl (g := fun _ => ENNReal.ofReal (Real.exp (-x) * x ^ n / (n.factorial : ℝ)))]
      · simp
      · intro r hr
        simp only [Finset.mem_range] at hr
        simp [Nat.succ_le_of_lt hr]
    · intro r hr
      simp only [Finset.mem_range, not_lt] at hr
      have : ¬ (r + 1 ≤ n) := by omega
      simp [this]
  simp_rw [hinner]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  have hterm : ∀ k : ℕ,
      ((k + 1 : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp (-x) * x ^ (k + 1) / ((k + 1).factorial : ℝ)) =
        ENNReal.ofReal (Real.exp (-x) * x) * ENNReal.ofReal (x ^ k / (k.factorial : ℝ)) := by
    intro k
    rw [← ENNReal.ofReal_natCast (k + 1), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) hx)]
    congr 1
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    have hne : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ennreal_tsum_exp x hx,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) hx)]
  congr 1
  calc
    Real.exp (-x) * x * Real.exp x = (Real.exp (-x) * Real.exp x) * x := by ring
    _ = x := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

lemma tsum_poisson_one_sub_pow (lam p α : ℝ) (hlam : 0 ≤ lam) (hp : p ∈ Ioo (0 : ℝ) 1) (hα : 0 ≤ α) :
    ∑' k : ℕ, ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * (α * (1 - p ^ k))) =
      ENNReal.ofReal (α * (1 - Real.exp (-lam * (1 - p)))) := by
  have h1 := ((hasSum_real_exp lam).sub (hasSum_real_exp (lam * p))).mul_left (α * Real.exp (-lam))
  have hf : (fun k : ℕ => Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * (α * (1 - p ^ k))) =
      fun i : ℕ => α * Real.exp (-lam) * (lam ^ i / (i.factorial : ℝ) - (lam * p) ^ i / (i.factorial : ℝ)) := by
    ext k
    rw [mul_pow]
    ring
  have ha : α * (1 - Real.exp (-lam * (1 - p))) =
      α * Real.exp (-lam) * (Real.exp lam - Real.exp (lam * p)) := by
    have hexp1 : Real.exp (-lam) * Real.exp lam = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hexp2 : Real.exp (-lam) * Real.exp (lam * p) = Real.exp (-lam * (1 - p)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      α * (1 - Real.exp (-lam * (1 - p)))
        = α * (Real.exp (-lam) * Real.exp lam - Real.exp (-lam) * Real.exp (lam * p)) := by
          rw [hexp1, hexp2]
      _ = α * Real.exp (-lam) * (Real.exp lam - Real.exp (lam * p)) := by ring
  have hsum : HasSum (fun k : ℕ => Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * (α * (1 - p ^ k)))
      (α * (1 - Real.exp (-lam * (1 - p)))) := by
    rw [hf, ha]
    exact h1
  have hnn : ∀ k : ℕ, 0 ≤ Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * (α * (1 - p ^ k)) := by
    intro k
    refine mul_nonneg (div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hlam _)) (Nat.cast_nonneg _))
      (mul_nonneg hα (sub_nonneg.mpr (pow_le_one₀ hp.1.le hp.2.le)))
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]

/-! ### Part 2: Feasibility reductions and the Poisson bound -/

noncomputable def totalRate (q : ℝ → ℕ → ℝ) (t : ℝ) : ENNReal :=
  ∑' r : ℕ, ENNReal.ofReal (q t (r + 1))

noncomputable def survProb (p : ℝ) (q : ℝ → ℕ → ℝ) (t : ℝ) : ℝ :=
  1 - (cumMass p q (min t 1)).toReal

lemma cumMass_le_one {p : ℝ} {q : ℝ → ℕ → ℝ} (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) :
    cumMass p q t ≤ 1 := by
  have h := hq.2.2 t ht 1 le_rfl
  exact le_trans le_add_self h

lemma survProb_eq_of_le_one {p : ℝ} {q : ℝ → ℕ → ℝ} {t : ℝ} (ht : t ≤ 1) :
    survProb p q t = 1 - (cumMass p q t).toReal := by
  simp [survProb, min_eq_left ht]

lemma survProb_nonneg {p : ℝ} {q : ℝ → ℕ → ℝ} (hq : IsFeasible p q) {t : ℝ} (ht : t ∈ Icc p 1) :
    0 ≤ survProb p q t := by
  rw [survProb_eq_of_le_one ht.2]
  have h1 := cumMass_le_one hq ht
  have h2 : (cumMass p q t).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
  linarith

lemma ofReal_survProb_add_cumMass {p : ℝ} {q : ℝ → ℕ → ℝ} (hq : IsFeasible p q)
    {t : ℝ} (ht : t ∈ Icc p 1) :
    ENNReal.ofReal (survProb p q t) + cumMass p q t = 1 := by
  rw [survProb_eq_of_le_one ht.2]
  have h1 : cumMass p q t ≤ 1 := cumMass_le_one hq ht
  have hfin : cumMass p q t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h1
  have hto : (cumMass p q t).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
  calc
    ENNReal.ofReal (1 - (cumMass p q t).toReal) + cumMass p q t
      = ENNReal.ofReal (1 - (cumMass p q t).toReal) + ENNReal.ofReal (cumMass p q t).toReal := by
        rw [ENNReal.ofReal_toReal hfin]
    _ = ENNReal.ofReal (1 - (cumMass p q t).toReal + (cumMass p q t).toReal) := by
        rw [← ENNReal.ofReal_add (sub_nonneg.mpr hto) ENNReal.toReal_nonneg]
    _ = 1 := by simp

lemma mul_q_le_survProb {p : ℝ} {q : ℝ → ℕ → ℝ} (hq : IsFeasible p q)
    {t : ℝ} (ht : t ∈ Icc p 1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    t * q t ℓ ≤ survProb p q t := by
  rw [survProb_eq_of_le_one ht.2]
  have h := hq.2.2 t ht ℓ hℓ
  have h1 : cumMass p q t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_add_self h)
  have h2 : ENNReal.ofReal (t * q t ℓ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hto := ENNReal.toReal_mono ENNReal.one_ne_top h
  rw [ENNReal.toReal_add h2 h1, ENNReal.toReal_one, ENNReal.toReal_ofReal'] at hto
  have hle : t * q t ℓ ≤ max (t * q t ℓ) 0 := le_max_left _ _
  linarith

lemma antitone_survProb {p : ℝ} {q : ℝ → ℕ → ℝ} (hq : IsFeasible p q) :
    Antitone (survProb p q) := by
  intro t₁ t₂ hle
  unfold survProb
  have hmin : min t₁ 1 ≤ min t₂ 1 := min_le_min_right 1 hle
  have hsub : Icc p (min t₁ 1) ⊆ Icc p (min t₂ 1) := Icc_subset_Icc_right hmin
  have hcm : cumMass p q (min t₁ 1) ≤ cumMass p q (min t₂ 1) :=
    lintegral_mono_set hsub
  have hfin : cumMass p q (min t₂ 1) ≠ ⊤ := by
    by_cases hp2 : p ≤ min t₂ 1
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top
        (cumMass_le_one hq ⟨hp2, min_le_right t₂ 1⟩)
    · have hempty : Icc p (min t₂ 1) = ∅ := Icc_eq_empty hp2
      simp [cumMass, hempty]
  have hto : (cumMass p q (min t₁ 1)).toReal ≤ (cumMass p q (min t₂ 1)).toReal :=
    ENNReal.toReal_mono hfin hcm
  linarith

lemma measurable_survProb {p : ℝ} {q : ℝ → ℕ → ℝ} (hq : IsFeasible p q) :
    Measurable (survProb p q) :=
  (antitone_survProb hq).measurable

lemma aemeasurable_totalRate {p : ℝ} {q : ℝ → ℕ → ℝ} (hq : IsFeasible p q) :
    AEMeasurable (totalRate q) (volume.restrict (Icc p 1)) := by
  unfold totalRate
  refine AEMeasurable.tsum fun r => ?_
  exact (hq.2.1 (r + 1) (Nat.succ_pos r)).aestronglyMeasurable.aemeasurable.ennreal_ofReal

lemma ofReal_Fk_eq {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {q : ℝ → ℕ → ℝ} (hq : IsFeasible p q) (k : ℕ) :
    ENNReal.ofReal (Fk p q k) =
      ∑' r : ℕ, ∫⁻ t in Icc p 1, ENNReal.ofReal (q t (r + 1) * nbTerm k (r + 1) t) := by
  unfold Fk
  have hint : ∀ ℓ : ℕ, 1 ≤ ℓ →
      IntegrableOn (fun t => q t ℓ * nbTerm k ℓ t) (Icc p 1) := by
    intro ℓ hℓ
    have hmeas : AEStronglyMeasurable (fun t => q t ℓ * nbTerm k ℓ t) (volume.restrict (Icc p 1)) := by
      refine (hq.2.1 ℓ hℓ).aestronglyMeasurable.mul ?_
      have hcont : Continuous (fun t => nbTerm k ℓ t) := by
        unfold nbTerm
        fun_prop
      exact hcont.aestronglyMeasurable
    refine Integrable.mono' (hq.2.1 ℓ hℓ) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans hp.1.le ht.1, ht.2⟩
    have hqnn : 0 ≤ q t ℓ := hq.1 t ht ℓ hℓ
    have hnbnn : 0 ≤ nbTerm k ℓ t := nbTerm_nonneg k ℓ t ht01
    have hnble : nbTerm k ℓ t ≤ 1 := nbTerm_le_one k ℓ hℓ t ht01
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hqnn hnbnn)]
    nlinarith
  have hterm : ∀ ℓ ∈ Finset.Icc 1 k,
      0 ≤ ∫ t in p..1, q t ℓ * nbTerm k ℓ t := by
    intro ℓ hℓ
    rw [intervalIntegral.integral_of_le hp.2.le]
    refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
    exact mul_nonneg (hq.1 t ⟨ht.1.le, ht.2⟩ ℓ (Finset.mem_Icc.mp hℓ).1)
      (nbTerm_nonneg k ℓ t ⟨le_trans hp.1.le ht.1.le, ht.2⟩)
  rw [ENNReal.ofReal_sum_of_nonneg hterm]
  have hterm_eq : ∀ ℓ ∈ Finset.Icc 1 k,
      ENNReal.ofReal (∫ t in p..1, q t ℓ * nbTerm k ℓ t) =
        ∫⁻ t in Icc p 1, ENNReal.ofReal (q t ℓ * nbTerm k ℓ t) := by
    intro ℓ hℓ
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
    rw [intervalIntegral.integral_of_le hp.2.le,
      Measure.restrict_congr_set Ioc_ae_eq_Icc]
    refine ofReal_integral_eq_lintegral_ofReal (hint ℓ hℓ1) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg (hq.1 t ht ℓ hℓ1) (nbTerm_nonneg k ℓ t ⟨le_trans hp.1.le ht.1, ht.2⟩)
  rw [Finset.sum_congr rfl hterm_eq]
  symm
  rw [tsum_eq_sum (s := Finset.range k)]
  · refine Finset.sum_nbij (fun r => r + 1) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_range, Finset.mem_Icc] at hr ⊢
      omega
    · intro r₁ _ r₂ _ h
      dsimp only at h
      omega
    · intro ℓ hℓ
      simp only [Finset.mem_coe, Finset.mem_Icc] at hℓ
      refine ⟨ℓ - 1, ?_, by simp; omega⟩
      simp only [Finset.mem_coe, Finset.mem_range]
      omega
    · intro _ _
      rfl
  · intro r hr
    simp only [Finset.mem_range, not_lt] at hr
    have hnb : ∀ t, nbTerm k (r + 1) t = 0 := by
      intro t
      unfold nbTerm
      rw [Finset.Icc_eq_empty (by omega)]
      simp
    simp [hnb]

lemma k_eq_one_bound {p α : ℝ} {q : ℝ → ℕ → ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hfeas : IsSDFeasible p q α) :
    ENNReal.ofReal α ≤ ∫⁻ t in Icc p 1, ENNReal.ofReal (survProb p q t / (1 - p)) := by
  have h1mp : 0 < 1 - p := sub_pos.mpr hp.2
  have hF1 : α * (1 - p) ≤ Fk p q 1 := by
    have h := hfeas.2.2.2 1 le_rfl
    rw [pow_one] at h
    exact (le_div_iff₀ h1mp).mp h
  have hF1_eq : Fk p q 1 = ∫ t in p..1, t * q t 1 := by
    unfold Fk nbTerm
    simp only [Finset.Icc_self, Finset.sum_singleton, tsub_self, Nat.choose_self, Nat.cast_one,
      pow_zero, mul_one, pow_one, one_mul]
    refine intervalIntegral.integral_congr fun t _ => mul_comm _ _
  have hle_enn : ENNReal.ofReal (α * (1 - p)) ≤ ∫⁻ t in Icc p 1, ENNReal.ofReal (survProb p q t) := by
    calc
      ENNReal.ofReal (α * (1 - p)) ≤ ENNReal.ofReal (Fk p q 1) := ENNReal.ofReal_le_ofReal hF1
      _ = ∑' r : ℕ, ∫⁻ t in Icc p 1, ENNReal.ofReal (q t (r + 1) * nbTerm 1 (r + 1) t) :=
          ofReal_Fk_eq hp hfeas.1 1
      _ = ∫⁻ t in Icc p 1, ENNReal.ofReal (q t 1 * t) := by
          rw [tsum_eq_single 0]
          · simp [nbTerm]
          · intro r hr
            have hnb : ∀ t, nbTerm 1 (r + 1) t = 0 := by
              intro t
              unfold nbTerm
              rw [Finset.Icc_eq_empty (by omega)]
              simp
            simp [hnb]
      _ ≤ ∫⁻ t in Icc p 1, ENNReal.ofReal (survProb p q t) := by
          refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
          rw [mul_comm]
          exact ENNReal.ofReal_le_ofReal (mul_q_le_survProb hfeas.1 ht le_rfl)
  have hmul : ENNReal.ofReal (1 / (1 - p)) * ENNReal.ofReal (α * (1 - p)) ≤
      ENNReal.ofReal (1 / (1 - p)) * ∫⁻ t in Icc p 1, ENNReal.ofReal (survProb p q t) := by
    gcongr
  rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one h1mp.le),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hmul
  have hsimp : 1 / (1 - p) * (α * (1 - p)) = α := by field_simp
  rw [hsimp] at hmul
  refine le_trans hmul (le_of_eq ?_)
  refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one h1mp.le), one_div_mul_eq_div]

lemma poisson_bound {p α : ℝ} {q : ℝ → ℕ → ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hfeas : IsSDFeasible p q α) {lam : ℝ} (hlam : 0 ≤ lam) :
    ENNReal.ofReal (α * (1 - Real.exp (-lam * (1 - p)))) ≤
      ∫⁻ t in Icc p 1, min (totalRate q t) (ENNReal.ofReal (lam * survProb p q t)) := by
  rw [← tsum_poisson_one_sub_pow lam p α hlam hp hfeas.2.1]
  have hstep1 :
      (∑' k : ℕ, ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * (α * (1 - p ^ k)))) ≤
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ)) *
          ENNReal.ofReal (Fk p q k) := by
    refine ENNReal.tsum_le_tsum fun k => ?_
    have hcoeff : 0 ≤ Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) :=
      div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hlam _)) (Nat.cast_nonneg _)
    rw [ENNReal.ofReal_mul hcoeff]
    rcases k with _ | k
    · simp
    · gcongr
      have h1mp : 0 < 1 - p ^ (k + 1) := sub_pos.mpr (pow_lt_one₀ hp.1.le hp.2 (Nat.succ_ne_zero k))
      exact (le_div_iff₀ h1mp).mp (hfeas.2.2.2 (k + 1) (Nat.succ_pos k))
  have hstep2 :
      (∑' k : ℕ, ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ)) *
          ENNReal.ofReal (Fk p q k)) =
        ∫⁻ t in Icc p 1, ∑' r : ℕ, ENNReal.ofReal (q t (r + 1)) * poissonTail (lam * t) (r + 1) := by
    have hFk_rew : ∀ k : ℕ,
        ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ)) * ENNReal.ofReal (Fk p q k) =
          ∫⁻ t in Icc p 1, ∑' r : ℕ,
            ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) *
              (q t (r + 1) * nbTerm k (r + 1) t)) := by
      intro k
      have hcoeff : 0 ≤ Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) :=
        div_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hlam _)) (Nat.cast_nonneg _)
      rw [ofReal_Fk_eq hp hfeas.1 k, ← ENNReal.tsum_mul_left]
      have hpull : ∀ r : ℕ,
          ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ)) *
              (∫⁻ t in Icc p 1, ENNReal.ofReal (q t (r + 1) * nbTerm k (r + 1) t)) =
            ∫⁻ t in Icc p 1,
              ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) *
                (q t (r + 1) * nbTerm k (r + 1) t)) := by
        intro r
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun t => ?_
        rw [← ENNReal.ofReal_mul hcoeff]
      simp_rw [hpull]
      rw [← lintegral_tsum]
      intro r
      have hcont : Continuous (fun t => nbTerm k (r + 1) t) := by unfold nbTerm; fun_prop
      have hq_meas : AEMeasurable (fun t => q t (r + 1)) (volume.restrict (Icc p 1)) :=
        (hfeas.1.2.1 (r + 1) (Nat.succ_pos r)).aestronglyMeasurable.aemeasurable
      exact ((hq_meas.mul hcont.aemeasurable).const_mul _).ennreal_ofReal
    simp_rw [hFk_rew]
    rw [← lintegral_tsum]
    · refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun r => ?_
      have hqnn : 0 ≤ q t (r + 1) := hfeas.1.1 t ht (r + 1) (Nat.succ_pos r)
      have hrew : ∀ k : ℕ,
          ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) *
              (q t (r + 1) * nbTerm k (r + 1) t)) =
            ENNReal.ofReal (q t (r + 1)) *
              ENNReal.ofReal (Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) *
                nbTerm k (r + 1) t) := by
        intro k
        rw [← ENNReal.ofReal_mul hqnn]
        congr 1
        ring
      simp_rw [hrew]
      rw [ENNReal.tsum_mul_left,
        tsum_poisson_nbTerm lam t hlam ⟨le_trans hp.1.le ht.1, ht.2⟩ (r + 1) (Nat.succ_pos r)]
    · intro k
      refine AEMeasurable.tsum fun r => ?_
      have hcont : Continuous (fun t => nbTerm k (r + 1) t) := by unfold nbTerm; fun_prop
      have hq_meas : AEMeasurable (fun t => q t (r + 1)) (volume.restrict (Icc p 1)) :=
        (hfeas.1.2.1 (r + 1) (Nat.succ_pos r)).aestronglyMeasurable.aemeasurable
      exact ((hq_meas.mul hcont.aemeasurable).const_mul _).ennreal_ofReal
  refine le_trans hstep1 ?_
  rw [hstep2]
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  have htpos : 0 < t := lt_of_lt_of_le hp.1 ht.1
  refine le_min ?_ ?_
  · unfold totalRate
    refine ENNReal.tsum_le_tsum fun r => ?_
    calc
      ENNReal.ofReal (q t (r + 1)) * poissonTail (lam * t) (r + 1)
        ≤ ENNReal.ofReal (q t (r + 1)) * 1 := by
          have := poissonTail_le_one (lam * t) (mul_nonneg hlam htpos.le) (r + 1)
          gcongr
      _ = ENNReal.ofReal (q t (r + 1)) := mul_one _
  · calc
      ∑' r : ℕ, ENNReal.ofReal (q t (r + 1)) * poissonTail (lam * t) (r + 1)
        ≤ ∑' r : ℕ, ENNReal.ofReal (survProb p q t / t) * poissonTail (lam * t) (r + 1) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          have h := mul_q_le_survProb hfeas.1 ht (Nat.succ_pos r)
          have hle : q t (r + 1) ≤ survProb p q t / t := (le_div_iff₀ htpos).mpr (by linarith)
          gcongr
      _ = ENNReal.ofReal (survProb p q t / t) * ENNReal.ofReal (lam * t) := by
          rw [ENNReal.tsum_mul_left, tsum_poissonTail_succ (lam * t) (mul_nonneg hlam htpos.le)]
      _ = ENNReal.ofReal (lam * survProb p q t) := by
          rw [← ENNReal.ofReal_mul (div_nonneg (survProb_nonneg hfeas.1 ht) htpos.le)]
          congr 1
          field_simp

/-! ### Part 3: The dual potential `D_ext`, `u_inc`, `Y`, `V`, `W` -/

noncomputable def D_ext (β w : ℝ) : ℝ :=
  if w ≤ 0 then β else if w ≤ 1 then w * (1 - Real.log w) + β else 1 + β

lemma D_ext_eq_of_mem_Icc (β : ℝ) {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) :
    D_ext β w = w * (1 - Real.log w) + β := by
  unfold D_ext
  by_cases h0 : w ≤ 0
  · have : w = 0 := le_antisymm h0 hw.1
    subst this
    simp
  · simp [h0, hw.2]

lemma D_ext_ge (β : ℝ) (w : ℝ) : β ≤ D_ext β w := by
  unfold D_ext
  split_ifs with h0 h1
  · exact le_rfl
  · have hw0 : 0 < w := not_le.mp h0
    have hlog : Real.log w ≤ 0 := Real.log_nonpos hw0.le h1
    nlinarith
  · linarith

lemma D_ext_le (β : ℝ) (w : ℝ) : D_ext β w ≤ 1 + β := by
  unfold D_ext
  split_ifs with h0 h1
  · linarith
  · have hw0 : 0 < w := not_le.mp h0
    have hlog : Real.log (1 / w) ≤ 1 / w - 1 :=
      Real.log_le_sub_one_of_pos (div_pos one_pos hw0)
    rw [one_div, Real.log_inv] at hlog
    have hmul : w * (-Real.log w) ≤ w * (w⁻¹ - 1) :=
      mul_le_mul_of_nonneg_left hlog hw0.le
    have hsimp : w * (w⁻¹ - 1) = 1 - w := by field_simp
    linarith
  · exact le_rfl

lemma D_ext_pos {β : ℝ} (hβ : 0 < β) (w : ℝ) : 0 < D_ext β w :=
  lt_of_lt_of_le hβ (D_ext_ge β w)

lemma continuous_D_ext (β : ℝ) : Continuous (D_ext β) := by
  have hmid : Continuous (fun w : ℝ => w * (1 - Real.log w) + β) := by
    have h1 : (fun w : ℝ => w * (1 - Real.log w) + β) = fun w => w - w * Real.log w + β := by
      ext w; ring
    rw [h1]
    exact (continuous_id.sub Real.continuous_mul_log).add continuous_const
  have hright : Continuous (fun w : ℝ => if w ≤ 1 then w * (1 - Real.log w) + β else 1 + β) := by
    refine Continuous.if_le hmid continuous_const continuous_id continuous_const ?_
    intro w hw
    simp [hw]
  refine Continuous.if_le continuous_const hright continuous_id continuous_const ?_
  intro w hw
  simp [hw]

lemma hasDerivAt_D_ext_Ioo (β : ℝ) {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (D_ext β) (-Real.log w) w := by
  have heq : D_ext β =ᶠ[𝓝 w] fun x => x * (1 - Real.log x) + β := by
    filter_upwards [Ioo_mem_nhds hw.1 hw.2] with x hx
    exact D_ext_eq_of_mem_Icc β ⟨hx.1.le, hx.2.le⟩
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have h1 : HasDerivAt (fun x : ℝ => 1 - Real.log x) (0 - w⁻¹) w :=
    (hasDerivAt_const w (1 : ℝ)).sub (Real.hasDerivAt_log hw.1.ne')
  have h2 := ((hasDerivAt_id' w).mul h1).add (hasDerivAt_const w β)
  refine h2.congr_deriv ?_
  field_simp [hw.1.ne']
  ring

lemma integral_inv_D_ext {s : ℝ} (hs : IsAlphaStar s) :
    ∫ w in (0 : ℝ)..1, 1 / D_ext (1 / s - 1) w = 1 := by
  have hcongr : ∀ w ∈ uIcc (0 : ℝ) 1,
      1 / D_ext (1 / s - 1) w = 1 / (w * (1 - Real.log w) + 1 / s - 1) := by
    intro w hw
    rw [Set.uIcc_of_le zero_le_one] at hw
    rw [D_ext_eq_of_mem_Icc _ hw]
    congr 1
    ring
  rw [intervalIntegral.integral_congr hcongr]
  exact hs.2.2

lemma integral_neg_log_div_D_ext_sq {β : ℝ} (hβ : 0 < β) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    ∫ w in y..1, (-Real.log w) / D_ext β w ^ 2 = 1 / D_ext β y - 1 / (1 + β) := by
  set F : ℝ → ℝ := fun w => -1 / (w * (1 - Real.log w) + β)
  have hDpos : ∀ w ∈ Icc y 1, 0 < w * (1 - Real.log w) + β := by
    intro w hw
    rw [← D_ext_eq_of_mem_Icc β ⟨le_trans hy.1.le hw.1, hw.2⟩]
    exact D_ext_pos hβ w
  have hderiv : ∀ w ∈ uIcc y 1,
      HasDerivAt F ((-Real.log w) / (w * (1 - Real.log w) + β) ^ 2) w := by
    intro w hw
    rw [Set.uIcc_of_le hy.2] at hw
    have hwpos : 0 < w := lt_of_lt_of_le hy.1 hw.1
    have hDne : w * (1 - Real.log w) + β ≠ 0 := (hDpos w hw).ne'
    have h1 : HasDerivAt (fun x : ℝ => x * (1 - Real.log x) + β) (-Real.log w) w := by
      have hlog : HasDerivAt (fun x : ℝ => 1 - Real.log x) (0 - w⁻¹) w :=
        (hasDerivAt_const w (1 : ℝ)).sub (Real.hasDerivAt_log hwpos.ne')
      have hmul := ((hasDerivAt_id' w).mul hlog).add (hasDerivAt_const w β)
      refine hmul.congr_deriv ?_
      field_simp [hwpos.ne']
      ring
    have hinv := (hasDerivAt_const w (-1 : ℝ)).div h1 hDne
    refine hinv.congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun w => (-Real.log w) / (w * (1 - Real.log w) + β) ^ 2) (uIcc y 1) := by
    rw [Set.uIcc_of_le hy.2]
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (Real.continuousOn_log.mono fun w hw => (lt_of_lt_of_le hy.1 hw.1).ne').neg
    · exact ((continuous_D_ext β).continuousOn.congr fun w hw =>
        (D_ext_eq_of_mem_Icc β ⟨le_trans hy.1.le hw.1, hw.2⟩).symm).pow 2
    · intro w hw
      exact pow_ne_zero 2 (hDpos w hw).ne'
  have hcongr : ∀ w ∈ uIcc y 1,
      (-Real.log w) / D_ext β w ^ 2 = (-Real.log w) / (w * (1 - Real.log w) + β) ^ 2 := by
    intro w hw
    rw [Set.uIcc_of_le hy.2] at hw
    rw [D_ext_eq_of_mem_Icc β ⟨le_trans hy.1.le hw.1, hw.2⟩]
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [F, Real.log_one, sub_zero, mul_one]
  rw [D_ext_eq_of_mem_Icc β ⟨hy.1.le, hy.2⟩]
  ring

lemma integral_one_sub_div_D_ext_sq {β : ℝ} (hβ : 0 < β) :
    1 / (1 + β) + ∫ w in (0 : ℝ)..1, (1 - w) / D_ext β w ^ 2 =
      (1 + β) * ∫ w in (0 : ℝ)..1, 1 / D_ext β w ^ 2 := by
  have hF_cont : ContinuousOn (fun w => w / D_ext β w) (Icc 0 1) :=
    continuousOn_id.div (continuous_D_ext β).continuousOn fun w _ => (D_ext_pos hβ w).ne'
  have hF_deriv : ∀ w ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun x => x / D_ext β x) ((w + β) / D_ext β w ^ 2) w := by
    intro w hw
    have hDne : D_ext β w ≠ 0 := (D_ext_pos hβ w).ne'
    have h := (hasDerivAt_id' w).div (hasDerivAt_D_ext_Ioo β hw) hDne
    refine h.congr_deriv ?_
    rw [D_ext_eq_of_mem_Icc β ⟨hw.1.le, hw.2.le⟩]
    ring
  have hint_wb : IntervalIntegrable (fun w => (w + β) / D_ext β w ^ 2) volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    exact (continuous_id.add continuous_const).div ((continuous_D_ext β).pow 2)
      fun w => pow_ne_zero 2 (D_ext_pos hβ w).ne'
  have hint_1w : IntervalIntegrable (fun w => (1 - w) / D_ext β w ^ 2) volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    exact (continuous_const.sub continuous_id).div ((continuous_D_ext β).pow 2)
      fun w => pow_ne_zero 2 (D_ext_pos hβ w).ne'
  have hFTC : ∫ w in (0 : ℝ)..1, (w + β) / D_ext β w ^ 2 = 1 / (1 + β) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hF_cont hF_deriv hint_wb]
    have hD1 : D_ext β 1 = 1 + β := by
      rw [D_ext_eq_of_mem_Icc β ⟨zero_le_one, le_rfl⟩]
      simp
    simp [hD1]
  rw [← hFTC, ← intervalIntegral.integral_add hint_wb hint_1w, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun w _ => ?_
  ring

noncomputable def u_inc (β y : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..y, 1 / D_ext β w

lemma hasDerivAt_u_inc {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    HasDerivAt (u_inc β) (1 / D_ext β y) y := by
  have hcont : Continuous (fun w => 1 / D_ext β w) :=
    continuous_const.div (continuous_D_ext β) fun w => (D_ext_pos hβ w).ne'
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 y)
    hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

lemma strictMono_u_inc {β : ℝ} (hβ : 0 < β) : StrictMono (u_inc β) := by
  refine strictMono_of_deriv_pos fun y => ?_
  rw [(hasDerivAt_u_inc hβ y).deriv]
  exact div_pos one_pos (D_ext_pos hβ y)

lemma u_inc_zero (β : ℝ) : u_inc β 0 = 0 := by
  simp [u_inc]

lemma u_inc_one {s : ℝ} (hs : IsAlphaStar s) : u_inc (1 / s - 1) 1 = 1 :=
  integral_inv_D_ext hs

lemma surjective_u_inc {s : ℝ} (hs : IsAlphaStar s) :
    Function.Surjective (u_inc (1 / s - 1)) := by
  set β := 1 / s - 1
  have hβ : 0 < β := by
    have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1
    linarith
  have hcont : Continuous (u_inc β) :=
    continuous_iff_continuousAt.mpr fun y => (hasDerivAt_u_inc hβ y).continuousAt
  intro z
  by_cases hz0 : z ≤ 0
  · refine ⟨β * z, ?_⟩
    have hbz : β * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ.le hz0
    unfold u_inc
    have hcongr : ∀ w ∈ uIcc (0 : ℝ) (β * z), 1 / D_ext β w = 1 / β := by
      intro w hw
      rw [Set.uIcc_of_ge hbz] at hw
      simp [D_ext, hw.2]
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    field_simp [hβ.ne']
  · push Not at hz0
    by_cases hz1 : z ≤ 1
    · have hmem : z ∈ Icc (u_inc β 0) (u_inc β 1) := by
        rw [u_inc_zero, u_inc_one hs]
        exact ⟨hz0.le, hz1⟩
      obtain ⟨y, _, hy⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn hmem
      exact ⟨y, hy⟩
    · push Not at hz1
      set y := 1 + (1 + β) * (z - 1)
      have hy1 : 1 ≤ y := by nlinarith
      refine ⟨y, ?_⟩
      have hcontD : Continuous (fun w => 1 / D_ext β w) :=
        continuous_const.div (continuous_D_ext β) fun w => (D_ext_pos hβ w).ne'
      unfold u_inc
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcontD.intervalIntegrable 0 1) (hcontD.intervalIntegrable 1 y)]
      rw [integral_inv_D_ext hs]
      have hcongr : ∀ w ∈ uIcc (1 : ℝ) y, 1 / D_ext β w = 1 / (1 + β) := by
        intro w hw
        rw [Set.uIcc_of_le hy1] at hw
        by_cases hw1 : w = 1
        · subst hw1
          rw [D_ext_eq_of_mem_Icc β ⟨zero_le_one, le_rfl⟩]
          simp
        · have hgt : 1 < w := lt_of_le_of_ne hw.1 (Ne.symm hw1)
          have hnot0 : ¬ w ≤ 0 := by linarith
          have hnot1 : ¬ w ≤ 1 := by linarith
          simp [D_ext, hnot0, hnot1]
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const]
      simp only [smul_eq_mul, y]
      have h1b : (1 + β) ≠ 0 := by linarith
      field_simp [h1b]
      ring

noncomputable def uHomeo {s : ℝ} (hs : IsAlphaStar s) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (u_inc (1 / s - 1))
    (strictMono_u_inc (by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith))
    (surjective_u_inc hs)).toHomeomorph

noncomputable def Y_fn {s : ℝ} (hs : IsAlphaStar s) (v : ℝ) : ℝ :=
  (uHomeo hs).symm (1 - v)

lemma u_inc_Y_fn {s : ℝ} (hs : IsAlphaStar s) (v : ℝ) :
    u_inc (1 / s - 1) (Y_fn hs v) = 1 - v :=
  (uHomeo hs).apply_symm_apply (1 - v)

lemma Y_fn_zero {s : ℝ} (hs : IsAlphaStar s) : Y_fn hs 0 = 1 := by
  have hβ : 0 < 1 / s - 1 := by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith
  have h : u_inc (1 / s - 1) (Y_fn hs 0) = u_inc (1 / s - 1) 1 := by
    calc
      u_inc (1 / s - 1) (Y_fn hs 0) = 1 - 0 := u_inc_Y_fn hs 0
      _ = 1 := sub_zero 1
      _ = u_inc (1 / s - 1) 1 := (u_inc_one hs).symm
  exact (strictMono_u_inc hβ).injective h

lemma Y_fn_one {s : ℝ} (hs : IsAlphaStar s) : Y_fn hs 1 = 0 := by
  have hβ : 0 < 1 / s - 1 := by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith
  have h : u_inc (1 / s - 1) (Y_fn hs 1) = u_inc (1 / s - 1) 0 := by
    calc
      u_inc (1 / s - 1) (Y_fn hs 1) = 1 - 1 := u_inc_Y_fn hs 1
      _ = 0 := sub_self 1
      _ = u_inc (1 / s - 1) 0 := (u_inc_zero (1 / s - 1)).symm
  exact (strictMono_u_inc hβ).injective h

lemma Y_fn_mem_Ioc {s : ℝ} (hs : IsAlphaStar s) {v : ℝ} (hv : v ∈ Ico (0 : ℝ) 1) :
    Y_fn hs v ∈ Ioc (0 : ℝ) 1 := by
  have hβ : 0 < 1 / s - 1 := by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith
  have hmono := strictMono_u_inc hβ
  constructor
  · by_contra hle
    push Not at hle
    have h1 : u_inc (1 / s - 1) (Y_fn hs v) ≤ u_inc (1 / s - 1) 0 := hmono.monotone hle
    rw [u_inc_Y_fn hs v, u_inc_zero] at h1
    linarith [hv.2]
  · by_contra hlt
    push Not at hlt
    have h1 : u_inc (1 / s - 1) 1 < u_inc (1 / s - 1) (Y_fn hs v) := hmono hlt
    rw [u_inc_Y_fn hs v, u_inc_one hs] at h1
    linarith [hv.1]

lemma hasDerivAt_Y_fn {s : ℝ} (hs : IsAlphaStar s) (v : ℝ) :
    HasDerivAt (Y_fn hs) (-D_ext (1 / s - 1) (Y_fn hs v)) v := by
  set β := 1 / s - 1
  have hβ : 0 < β := by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith
  have hinv : HasDerivAt (uHomeo hs).symm (D_ext β ((uHomeo hs).symm (1 - v))) (1 - v) := by
    have h1 := (hasDerivAt_u_inc hβ ((uHomeo hs).symm (1 - v))).of_local_left_inverse
      ((uHomeo hs).symm.continuous.continuousAt)
      (div_ne_zero one_ne_zero (D_ext_pos hβ _).ne')
      (Eventually.of_forall fun z => (uHomeo hs).apply_symm_apply z)
    simpa [one_div] using h1
  have hlin : HasDerivAt (fun x : ℝ => 1 - x) (-1) v :=
    ((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id' v)).congr_deriv (by ring)
  exact (hinv.comp v hlin).congr_deriv (by unfold Y_fn; ring)

noncomputable def V_fn {s : ℝ} (hs : IsAlphaStar s) (v : ℝ) : ℝ :=
  ∫ w in (0 : ℝ)..(Y_fn hs v), 1 / D_ext (1 / s - 1) w ^ 2

noncomputable def W_fn {s : ℝ} (hs : IsAlphaStar s) (p t : ℝ) : ℝ :=
  V_fn hs ((t - p) / (1 - p))

noncomputable def y_fn {s : ℝ} (hs : IsAlphaStar s) (p t : ℝ) : ℝ :=
  Y_fn hs ((t - p) / (1 - p))

lemma hasDerivAt_V_fn {s : ℝ} (hs : IsAlphaStar s) (v : ℝ) :
    HasDerivAt (V_fn hs) (-1 / D_ext (1 / s - 1) (Y_fn hs v)) v := by
  set β := 1 / s - 1
  have hβ : 0 < β := by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith
  have hcont : Continuous (fun w => 1 / D_ext β w ^ 2) :=
    continuous_const.div ((continuous_D_ext β).pow 2) fun w => pow_ne_zero 2 (D_ext_pos hβ w).ne'
  have hint_deriv : HasDerivAt (fun y => ∫ w in (0 : ℝ)..y, 1 / D_ext β w ^ 2)
      (1 / D_ext β (Y_fn hs v) ^ 2) (Y_fn hs v) :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 _)
      hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  refine (hint_deriv.comp v (hasDerivAt_Y_fn hs v)).congr_deriv ?_
  have hne : D_ext β (Y_fn hs v) ≠ 0 := (D_ext_pos hβ _).ne'
  change 1 / D_ext β (Y_fn hs v) ^ 2 * -D_ext β (Y_fn hs v) = -1 / D_ext β (Y_fn hs v)
  field_simp [hne]

lemma hasDerivAt_W_fn {s : ℝ} (hs : IsAlphaStar s) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    HasDerivAt (W_fn hs p) (-1 / ((1 - p) * D_ext (1 / s - 1) (y_fn hs p t))) t := by
  have h1mp : (1 - p) ≠ 0 := (sub_pos.mpr hp.2).ne'
  have hβ : 0 < 1 / s - 1 := by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith
  have hDne : D_ext (1 / s - 1) (y_fn hs p t) ≠ 0 := (D_ext_pos hβ _).ne'
  have hlin : HasDerivAt (fun x : ℝ => (x - p) / (1 - p)) (1 / (1 - p)) t :=
    (((hasDerivAt_id' t).sub_const p).div_const (1 - p)).congr_deriv (by ring)
  refine ((hasDerivAt_V_fn hs ((t - p) / (1 - p))).comp t hlin).congr_deriv ?_
  unfold y_fn
  field_simp [h1mp, hDne]

lemma W_fn_p {s : ℝ} (hs : IsAlphaStar s) (p : ℝ) :
    W_fn hs p p = ∫ w in (0 : ℝ)..1, 1 / D_ext (1 / s - 1) w ^ 2 := by
  simp [W_fn, V_fn, Y_fn_zero hs]

lemma W_fn_one {s : ℝ} (hs : IsAlphaStar s) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    W_fn hs p 1 = 0 := by
  have h1mp : (1 - p) ≠ 0 := (sub_pos.mpr hp.2).ne'
  simp [W_fn, V_fn, div_self h1mp, Y_fn_one hs]

lemma W_fn_p_pos {s : ℝ} (hs : IsAlphaStar s) (p : ℝ) : 0 < W_fn hs p p := by
  set β := 1 / s - 1
  have hβ : 0 < β := by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith
  rw [W_fn_p hs p]
  have hcont : Continuous (fun w => 1 / D_ext β w ^ 2) :=
    continuous_const.div ((continuous_D_ext β).pow 2) fun w => pow_ne_zero 2 (D_ext_pos hβ w).ne'
  have hlow : ∀ w ∈ Icc (0 : ℝ) 1, 1 / (1 + β) ^ 2 ≤ 1 / D_ext β w ^ 2 := by
    intro w _
    have hle : D_ext β w ≤ 1 + β := D_ext_le β w
    have hpos : 0 < D_ext β w := D_ext_pos hβ w
    exact one_div_le_one_div_of_le (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hle 2)
  have hle : ∫ w in (0 : ℝ)..1, (1 / (1 + β) ^ 2 : ℝ) ≤ ∫ w in (0 : ℝ)..1, 1 / D_ext β w ^ 2 :=
    intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
      (hcont.intervalIntegrable 0 1) hlow
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at hle
  have hpos : (0 : ℝ) < 1 / (1 + β) ^ 2 := by positivity
  linarith

lemma W_fn_eq_integral_deriv {s : ℝ} (hs : IsAlphaStar s) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    {τ : ℝ} (_hτ : τ ∈ Icc p 1) :
    ∫ t in τ..1, 1 / ((1 - p) * D_ext (1 / s - 1) (y_fn hs p t)) = W_fn hs p τ := by
  set β := 1 / s - 1
  have hβ : 0 < β := by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith
  have h1mp : 0 < 1 - p := sub_pos.mpr hp.2
  have hcont_y : Continuous (y_fn hs p) := by
    unfold y_fn Y_fn
    exact (uHomeo hs).symm.continuous.comp (continuous_const.sub ((continuous_id.sub continuous_const).div_const _))
  have hcont : Continuous (fun t => 1 / ((1 - p) * D_ext β (y_fn hs p t))) :=
    continuous_const.div (continuous_const.mul ((continuous_D_ext β).comp hcont_y))
      fun t => mul_ne_zero h1mp.ne' (D_ext_pos hβ _).ne'
  have hderiv : ∀ t ∈ uIcc τ 1,
      HasDerivAt (fun x => -W_fn hs p x) (1 / ((1 - p) * D_ext β (y_fn hs p t))) t := by
    intro t _
    exact (hasDerivAt_W_fn hs hp t).neg.congr_deriv (by rw [neg_div, neg_neg])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable τ 1),
    W_fn_one hs hp]
  ring

/-! ### Part 4: Tonelli identity for the dual potential -/

lemma lintegral_W_identity {s : ℝ} (hs : IsAlphaStar s) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    {q : ℝ → ℕ → ℝ} (hq : IsFeasible p q) :
    (∫⁻ t in Icc p 1, totalRate q t * ENNReal.ofReal (W_fn hs p t)) +
      (∫⁻ t in Icc p 1,
        ENNReal.ofReal (survProb p q t / ((1 - p) * D_ext (1 / s - 1) (y_fn hs p t)))) =
      ENNReal.ofReal (W_fn hs p p) := by
  set β := 1 / s - 1
  have hβ : 0 < β := by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith
  have h1mp : 0 < 1 - p := sub_pos.mpr hp.2
  set g : ℝ → ℝ := fun t => 1 / ((1 - p) * D_ext β (y_fn hs p t))
  have hcont_y : Continuous (y_fn hs p) := by
    unfold y_fn Y_fn
    exact (uHomeo hs).symm.continuous.comp
      (continuous_const.sub ((continuous_id.sub continuous_const).div_const _))
  have hcont_g : Continuous g :=
    continuous_const.div (continuous_const.mul ((continuous_D_ext β).comp hcont_y))
      fun t => mul_ne_zero h1mp.ne' (D_ext_pos hβ _).ne'
  have hg_pos : ∀ t, 0 < g t := fun t => div_pos one_pos (mul_pos h1mp (D_ext_pos hβ _))
  have htonelli :
      (∫⁻ t in Icc p 1, cumMass p q t * ENNReal.ofReal (g t)) =
        ∫⁻ τ in Icc p 1, totalRate q τ * ENNReal.ofReal (W_fn hs p τ) := by
    have hlhs :
        (∫⁻ t in Icc p 1, cumMass p q t * ENNReal.ofReal (g t)) =
          ∫⁻ t in Icc p 1, ∫⁻ τ in Icc p 1,
            Set.indicator {z : ℝ × ℝ | z.2 ≤ z.1}
              (fun z => totalRate q z.2 * ENNReal.ofReal (g z.1)) (t, τ) := by
      refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
      unfold cumMass totalRate
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      have hset : Icc p t = Iic t ∩ Icc p 1 := by
        ext τ
        simp only [mem_Icc, mem_inter_iff, mem_Iic]
        exact ⟨fun h => ⟨h.2, h.1, le_trans h.2 ht.2⟩, fun h => ⟨h.2.1, h.1⟩⟩
      rw [hset, ← Measure.restrict_restrict measurableSet_Iic,
        ← lintegral_indicator measurableSet_Iic]
      refine lintegral_congr fun τ => ?_
      by_cases hτt : τ ≤ t <;> simp [Set.indicator, hτt]
    rw [hlhs]
    have hmeas_ind : AEMeasurable
        (Function.uncurry fun t τ =>
          Set.indicator {z : ℝ × ℝ | z.2 ≤ z.1}
            (fun z => totalRate q z.2 * ENNReal.ofReal (g z.1)) (t, τ))
        ((volume.restrict (Icc p 1)).prod (volume.restrict (Icc p 1))) := by
      have hset : MeasurableSet {z : ℝ × ℝ | z.2 ≤ z.1} :=
        isClosed_le continuous_snd continuous_fst |>.measurableSet
      have h1 : AEMeasurable (fun z : ℝ × ℝ => totalRate q z.2)
          ((volume.restrict (Icc p 1)).prod (volume.restrict (Icc p 1))) :=
        (aemeasurable_totalRate hq).comp_snd
      have h2 : AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (g z.1))
          ((volume.restrict (Icc p 1)).prod (volume.restrict (Icc p 1))) :=
        (hcont_g.measurable.comp measurable_fst).ennreal_ofReal.aemeasurable
      exact (h1.mul h2).indicator hset
    rw [lintegral_lintegral_swap hmeas_ind]
    refine setLIntegral_congr_fun measurableSet_Icc fun τ hτ => ?_
    have hrew :
        (∫⁻ t in Icc p 1,
          Set.indicator {z : ℝ × ℝ | z.2 ≤ z.1}
            (fun z => totalRate q z.2 * ENNReal.ofReal (g z.1)) (t, τ)) =
          totalRate q τ * ∫⁻ t in Icc τ 1, ENNReal.ofReal (g t) := by
      have hset : Icc τ 1 = Ici τ ∩ Icc p 1 := by
        ext t
        simp only [mem_Icc, mem_inter_iff, mem_Ici]
        exact ⟨fun h => ⟨h.1, le_trans hτ.1 h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rw [hset, ← Measure.restrict_restrict measurableSet_Ici,
        ← lintegral_indicator measurableSet_Ici, ← lintegral_const_mul'']
      · refine lintegral_congr fun t => ?_
        by_cases hτt : τ ≤ t <;> simp [Set.indicator, hτt]
      · exact (hcont_g.measurable.ennreal_ofReal.indicator measurableSet_Ici).aemeasurable
    rw [hrew]
    congr 1
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc,
      ← ofReal_integral_eq_lintegral_ofReal (hcont_g.integrableOn_Ioc)
        (Eventually.of_forall fun t => (hg_pos t).le),
      ← intervalIntegral.integral_of_le hτ.2,
      W_fn_eq_integral_deriv hs hp hτ]
  have hsum :
      (∫⁻ t in Icc p 1, cumMass p q t * ENNReal.ofReal (g t)) +
        (∫⁻ t in Icc p 1, ENNReal.ofReal (survProb p q t / ((1 - p) * D_ext β (y_fn hs p t)))) =
        ∫⁻ t in Icc p 1, ENNReal.ofReal (g t) := by
    have hmeas1 : AEMeasurable (fun t => cumMass p q t * ENNReal.ofReal (g t))
        (volume.restrict (Icc p 1)) := by
      have hcm_mono : Monotone (cumMass p q) := fun t₁ t₂ h =>
        lintegral_mono_set (Icc_subset_Icc_right h)
      exact (hcm_mono.measurable.mul hcont_g.measurable.ennreal_ofReal).aemeasurable
    have hmeas2 : AEMeasurable
        (fun t => ENNReal.ofReal (survProb p q t / ((1 - p) * D_ext β (y_fn hs p t))))
        (volume.restrict (Icc p 1)) :=
      ((measurable_survProb hq).mul hcont_g.measurable).ennreal_ofReal.aemeasurable.congr
        (Eventually.of_forall fun t => by simp [g, div_eq_mul_inv])
    rw [← lintegral_add_left' hmeas1]
    refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    have heq : ENNReal.ofReal (survProb p q t / ((1 - p) * D_ext β (y_fn hs p t))) =
        ENNReal.ofReal (survProb p q t) * ENNReal.ofReal (g t) := by
      rw [← ENNReal.ofReal_mul (survProb_nonneg hq ht)]
      congr 1
      simp [g, div_eq_mul_inv]
    rw [heq, ← add_mul, add_comm, ofReal_survProb_add_cumMass hq ht, one_mul]
  rw [← htonelli, hsum]
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (hcont_g.integrableOn_Ioc)
      (Eventually.of_forall fun t => (hg_pos t).le),
    ← intervalIntegral.integral_of_le hp.2.le,
    W_fn_eq_integral_deriv hs hp ⟨le_rfl, hp.2.le⟩]

/-! ### Part 5: Combining the bounds to prove `α ≤ s` for any feasible `(q, α)` -/

lemma alpha_le_alphaStar {p s α : ℝ} {q : ℝ → ℕ → ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hs : IsAlphaStar s) (hfeas : IsSDFeasible p q α) :
    α ≤ s := by
  set β := 1 / s - 1
  have hβ : 0 < β := by have : 1 < 1 / s := (one_lt_div hs.1).mpr hs.2.1; linarith
  have h1mp : 0 < 1 - p := sub_pos.mpr hp.2
  have h1b : 1 + β = 1 / s := by simp [β]
  -- Step 1: Integrate the Poisson bound against 1 / D_ext(w)^2 over w ∈ (0, 1).
  have hstep1 :
      ∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (α * (1 - w) / D_ext β w ^ 2) ≤
        ∫⁻ w in Ioo (0 : ℝ) 1, ∫⁻ t in Icc p 1,
          ENNReal.ofReal (1 / D_ext β w ^ 2) *
            min (totalRate q t) (ENNReal.ofReal ((-Real.log w) / (1 - p) * survProb p q t)) := by
    refine setLIntegral_mono' measurableSet_Ioo fun w hw => ?_
    have hlam : 0 ≤ (-Real.log w) / (1 - p) :=
      div_nonneg (neg_nonneg.mpr (Real.log_nonpos hw.1.le hw.2.le)) h1mp.le
    have hpb := poisson_bound hp hfeas hlam
    have hexp : Real.exp (-((-Real.log w) / (1 - p)) * (1 - p)) = w := by
      have harg : -((-Real.log w) / (1 - p)) * (1 - p) = Real.log w := by
        field_simp [h1mp.ne']
      rw [harg, Real.exp_log hw.1]
    rw [hexp] at hpb
    have hmul : ENNReal.ofReal (1 / D_ext β w ^ 2) * ENNReal.ofReal (α * (1 - w)) ≤
        ENNReal.ofReal (1 / D_ext β w ^ 2) *
          ∫⁻ t in Icc p 1, min (totalRate q t) (ENNReal.ofReal ((-Real.log w) / (1 - p) * survProb p q t)) := by
      gcongr
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hmul
    have hD2 : 0 ≤ 1 / D_ext β w ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
    rw [← ENNReal.ofReal_mul hD2] at hmul
    convert hmul using 2
    ring
  -- Step 2: Tonelli swap on (w, t) ∈ (0, 1) × [p, 1].
  have hmeas_prod : AEMeasurable
      (Function.uncurry fun w t =>
        ENNReal.ofReal (1 / D_ext β w ^ 2) *
          min (totalRate q t) (ENNReal.ofReal ((-Real.log w) / (1 - p) * survProb p q t)))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Icc p 1))) := by
    have h1 : AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (1 / D_ext β z.1 ^ 2))
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Icc p 1))) :=
      ((continuous_const.div ((continuous_D_ext β).pow 2)
        fun w => pow_ne_zero 2 (D_ext_pos hβ w).ne').measurable.comp measurable_fst).ennreal_ofReal.aemeasurable
    have h2 : AEMeasurable (fun z : ℝ × ℝ => totalRate q z.2)
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Icc p 1))) :=
      (aemeasurable_totalRate hfeas.1).comp_snd
    have h3 : AEMeasurable
        (fun z : ℝ × ℝ => ENNReal.ofReal ((-Real.log z.1) / (1 - p) * survProb p q z.2))
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Icc p 1))) := by
      have hm1 : Measurable (fun z : ℝ × ℝ => (-Real.log z.1) / (1 - p)) :=
        ((Real.measurable_log.comp measurable_fst).neg).div_const (1 - p)
      have hm2 : Measurable (fun z : ℝ × ℝ => survProb p q z.2) :=
        (measurable_survProb hfeas.1).comp measurable_snd
      exact (hm1.mul hm2).ennreal_ofReal.aemeasurable
    exact h1.mul (h2.min h3)
  rw [lintegral_lintegral_swap hmeas_prod] at hstep1
  -- Step 3: Split the w-integral at y_fn hs p t for each t ∈ [p, 1).
  have hstep2 :
      (∫⁻ t in Icc p 1, ∫⁻ w in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (1 / D_ext β w ^ 2) *
            min (totalRate q t) (ENNReal.ofReal ((-Real.log w) / (1 - p) * survProb p q t))) ≤
        (∫⁻ t in Icc p 1, totalRate q t * ENNReal.ofReal (W_fn hs p t)) +
        (∫⁻ t in Icc p 1,
          ENNReal.ofReal (survProb p q t / (1 - p) *
            (1 / D_ext β (y_fn hs p t) - 1 / (1 + β)))) := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Icc.symm]
    have hmeas_a : AEMeasurable (fun t => totalRate q t * ENNReal.ofReal (W_fn hs p t))
        (volume.restrict (Ico p 1)) := by
      have hcont_W : Continuous (W_fn hs p) :=
        continuous_iff_continuousAt.mpr fun t => (hasDerivAt_W_fn hs hp t).continuousAt
      have htr : AEMeasurable (totalRate q) (volume.restrict (Ico p 1)) := by
        rw [Measure.restrict_congr_set Ico_ae_eq_Icc]
        exact aemeasurable_totalRate hfeas.1
      exact htr.mul hcont_W.measurable.ennreal_ofReal.aemeasurable
    rw [← lintegral_add_left' hmeas_a]
    refine setLIntegral_mono' measurableSet_Ico fun t ht => ?_
    have hv : (t - p) / (1 - p) ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr ht.1) h1mp.le
      · exact (div_lt_one h1mp).mpr (by linarith [ht.2])
    have hy : y_fn hs p t ∈ Ioc (0 : ℝ) 1 := Y_fn_mem_Ioc hs hv
    have hunion : Ioo (0 : ℝ) 1 = Ioo 0 (y_fn hs p t) ∪ Ico (y_fn hs p t) 1 := by
      ext w
      simp only [mem_Ioo, mem_union, mem_Ico]
      constructor
      · intro hw
        by_cases hwy : w < y_fn hs p t
        · exact Or.inl ⟨hw.1, hwy⟩
        · exact Or.inr ⟨not_lt.mp hwy, hw.2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, lt_of_lt_of_le h2 hy.2⟩
        · exact ⟨lt_of_lt_of_le hy.1 h1, h2⟩
    have hdisj : Disjoint (Ioo (0 : ℝ) (y_fn hs p t)) (Ico (y_fn hs p t) 1) := by
      rw [Set.disjoint_left]
      intro w hw1 hw2
      linarith [hw1.2, hw2.1]
    rw [hunion, lintegral_union measurableSet_Ico hdisj]
    refine add_le_add ?_ ?_
    · -- On w ∈ (0, y_fn hs p t), bound min by totalRate q t
      calc
        (∫⁻ w in Ioo 0 (y_fn hs p t),
            ENNReal.ofReal (1 / D_ext β w ^ 2) *
              min (totalRate q t) (ENNReal.ofReal ((-Real.log w) / (1 - p) * survProb p q t)))
          ≤ ∫⁻ w in Ioo 0 (y_fn hs p t), ENNReal.ofReal (1 / D_ext β w ^ 2) * totalRate q t := by
            refine setLIntegral_mono' measurableSet_Ioo fun w _ => ?_
            have := min_le_left (totalRate q t)
              (ENNReal.ofReal ((-Real.log w) / (1 - p) * survProb p q t))
            gcongr
        _ = totalRate q t * ∫⁻ w in Ioo 0 (y_fn hs p t), ENNReal.ofReal (1 / D_ext β w ^ 2) := by
            simp_rw [mul_comm _ (totalRate q t)]
            have hcont : Continuous (fun w => 1 / D_ext β w ^ 2) :=
              continuous_const.div ((continuous_D_ext β).pow 2)
                fun w => pow_ne_zero 2 (D_ext_pos hβ w).ne'
            rw [lintegral_const_mul'' _ hcont.measurable.ennreal_ofReal.aemeasurable]
        _ = totalRate q t * ENNReal.ofReal (W_fn hs p t) := by
            congr 1
            have hcont : Continuous (fun w => 1 / D_ext β w ^ 2) :=
              continuous_const.div ((continuous_D_ext β).pow 2)
                fun w => pow_ne_zero 2 (D_ext_pos hβ w).ne'
            rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
              ← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Ioc
                (Eventually.of_forall fun w => div_nonneg zero_le_one (sq_nonneg _)),
              ← intervalIntegral.integral_of_le hy.1.le]
            rfl
    · -- On w ∈ [y_fn hs p t, 1), bound min by (-log w) / (1 - p) * survProb p q t
      have hsp_nn : 0 ≤ survProb p q t / (1 - p) :=
        div_nonneg (survProb_nonneg hfeas.1 ⟨ht.1, ht.2.le⟩) h1mp.le
      calc
        (∫⁻ w in Ico (y_fn hs p t) 1,
            ENNReal.ofReal (1 / D_ext β w ^ 2) *
              min (totalRate q t) (ENNReal.ofReal ((-Real.log w) / (1 - p) * survProb p q t)))
          ≤ ∫⁻ w in Ico (y_fn hs p t) 1,
              ENNReal.ofReal (1 / D_ext β w ^ 2) *
                ENNReal.ofReal ((-Real.log w) / (1 - p) * survProb p q t) := by
            refine setLIntegral_mono' measurableSet_Ico fun w _ => ?_
            have := min_le_right (totalRate q t)
              (ENNReal.ofReal ((-Real.log w) / (1 - p) * survProb p q t))
            gcongr
        _ = ENNReal.ofReal (survProb p q t / (1 - p)) *
              ∫⁻ w in Ico (y_fn hs p t) 1, ENNReal.ofReal ((-Real.log w) / D_ext β w ^ 2) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine setLIntegral_congr_fun measurableSet_Ico fun w _ => ?_
            rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one (sq_nonneg _)),
              ← ENNReal.ofReal_mul hsp_nn]
            congr 1
            ring
        _ = ENNReal.ofReal (survProb p q t / (1 - p) *
              (1 / D_ext β (y_fn hs p t) - 1 / (1 + β))) := by
            rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
            have hcont_log : ContinuousOn (fun w => (-Real.log w) / D_ext β w ^ 2)
                (Icc (y_fn hs p t) 1) := by
              refine ContinuousOn.div ?_ ((continuous_D_ext β).continuousOn.pow 2)
                fun w _ => pow_ne_zero 2 (D_ext_pos hβ w).ne'
              exact (Real.continuousOn_log.mono fun w hw => (lt_of_lt_of_le hy.1 hw.1).ne').neg
            have hint_log : IntegrableOn (fun w => (-Real.log w) / D_ext β w ^ 2)
                (Ioc (y_fn hs p t) 1) :=
              (hcont_log.integrableOn_Icc).mono_set Ioc_subset_Icc_self
            have hnn_log : 0 ≤ᵐ[volume.restrict (Ioc (y_fn hs p t) 1)]
                fun w => (-Real.log w) / D_ext β w ^ 2 := by
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
              exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (lt_trans hy.1 hw.1).le hw.2))
                (sq_nonneg _)
            rw [← ofReal_integral_eq_lintegral_ofReal hint_log hnn_log,
              ← intervalIntegral.integral_of_le hy.2,
              integral_neg_log_div_D_ext_sq hβ hy,
              ← ENNReal.ofReal_mul hsp_nn]
  -- Step 4: Evaluate the LHS of hstep1.
  have hlhs_eval :
      (∫⁻ w in Ioo (0 : ℝ) 1, ENNReal.ofReal (α * (1 - w) / D_ext β w ^ 2)) =
        ENNReal.ofReal (α * ∫ w in (0 : ℝ)..1, (1 - w) / D_ext β w ^ 2) := by
    have hcont : Continuous (fun w => α * (1 - w) / D_ext β w ^ 2) :=
      (continuous_const.mul (continuous_const.sub continuous_id)).div
        ((continuous_D_ext β).pow 2) fun w => pow_ne_zero 2 (D_ext_pos hβ w).ne'
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      ← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Ioc]
    · rw [← intervalIntegral.integral_of_le zero_le_one]
      congr 1
      have hrew : (fun w => α * (1 - w) / D_ext β w ^ 2) =
          fun w => α * ((1 - w) / D_ext β w ^ 2) := by ext w; ring
      rw [hrew, intervalIntegral.integral_const_mul]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
      exact div_nonneg (mul_nonneg hfeas.2.1 (sub_nonneg.mpr hw.2)) (sq_nonneg _)
  -- Step 5: Scale k = 1 bound by 1 / (1 + β) and add to Step 1 + Step 2.
  have hk1 :
      ENNReal.ofReal (α * (1 / (1 + β))) ≤
        ∫⁻ t in Icc p 1, ENNReal.ofReal (survProb p q t / (1 - p) * (1 / (1 + β))) := by
    have hk1_base := k_eq_one_bound hp hfeas
    have h : ENNReal.ofReal α * ENNReal.ofReal (1 / (1 + β)) ≤
        (∫⁻ t in Icc p 1, ENNReal.ofReal (survProb p q t / (1 - p))) *
          ENNReal.ofReal (1 / (1 + β)) := by
      gcongr
    rw [← ENNReal.ofReal_mul hfeas.2.1, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top] at h
    refine le_trans h (le_of_eq ?_)
    refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    rw [← ENNReal.ofReal_mul (div_nonneg (survProb_nonneg hfeas.1 ht) h1mp.le)]
  have hcomb :
      ENNReal.ofReal (α * (1 / (1 + β))) +
        ENNReal.ofReal (α * ∫ w in (0 : ℝ)..1, (1 - w) / D_ext β w ^ 2) ≤
      (∫⁻ t in Icc p 1, totalRate q t * ENNReal.ofReal (W_fn hs p t)) +
        ((∫⁻ t in Icc p 1,
            ENNReal.ofReal (survProb p q t / (1 - p) *
              (1 / D_ext β (y_fn hs p t) - 1 / (1 + β)))) +
          (∫⁻ t in Icc p 1,
            ENNReal.ofReal (survProb p q t / (1 - p) * (1 / (1 + β))))) := by
    have hmain := le_trans hstep1 hstep2
    rw [hlhs_eval] at hmain
    calc
      ENNReal.ofReal (α * (1 / (1 + β))) +
          ENNReal.ofReal (α * ∫ w in (0 : ℝ)..1, (1 - w) / D_ext β w ^ 2)
        ≤ (∫⁻ t in Icc p 1, ENNReal.ofReal (survProb p q t / (1 - p) * (1 / (1 + β)))) +
            ((∫⁻ t in Icc p 1, totalRate q t * ENNReal.ofReal (W_fn hs p t)) +
              (∫⁻ t in Icc p 1,
                ENNReal.ofReal (survProb p q t / (1 - p) *
                  (1 / D_ext β (y_fn hs p t) - 1 / (1 + β))))) :=
          add_le_add hk1 hmain
      _ = _ := by ac_rfl
  -- Simplify LHS of hcomb
  have hcont_1w : Continuous (fun w => (1 - w) / D_ext β w ^ 2) :=
    (continuous_const.sub continuous_id).div ((continuous_D_ext β).pow 2)
      fun w => pow_ne_zero 2 (D_ext_pos hβ w).ne'
  have hint_1w_nn : 0 ≤ ∫ w in (0 : ℝ)..1, (1 - w) / D_ext β w ^ 2 := by
    refine intervalIntegral.integral_nonneg zero_le_one fun w hw => ?_
    exact div_nonneg (sub_nonneg.mpr hw.2) (sq_nonneg _)
  have hLHS_eq :
      ENNReal.ofReal (α * (1 / (1 + β))) +
          ENNReal.ofReal (α * ∫ w in (0 : ℝ)..1, (1 - w) / D_ext β w ^ 2) =
        ENNReal.ofReal (α * (1 + β) * W_fn hs p p) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hfeas.2.1 (by positivity))
      (mul_nonneg hfeas.2.1 hint_1w_nn)]
    congr 1
    rw [← mul_add, integral_one_sub_div_D_ext_sq hβ, W_fn_p hs p]
    ring
  -- Simplify the sum of the two survProb integrals on the RHS of hcomb
  have hRHS_sub :
      (∫⁻ t in Icc p 1,
          ENNReal.ofReal (survProb p q t / (1 - p) *
            (1 / D_ext β (y_fn hs p t) - 1 / (1 + β)))) +
        (∫⁻ t in Icc p 1,
          ENNReal.ofReal (survProb p q t / (1 - p) * (1 / (1 + β)))) =
        ∫⁻ t in Icc p 1,
          ENNReal.ofReal (survProb p q t / ((1 - p) * D_ext β (y_fn hs p t))) := by
    have hcont_y : Continuous (y_fn hs p) := by
      unfold y_fn Y_fn
      exact (uHomeo hs).symm.continuous.comp
        (continuous_const.sub ((continuous_id.sub continuous_const).div_const _))
    have hm1 : AEMeasurable
        (fun t => ENNReal.ofReal (survProb p q t / (1 - p) *
          (1 / D_ext β (y_fn hs p t) - 1 / (1 + β))))
        (volume.restrict (Icc p 1)) := by
      have hm_sp := (measurable_survProb hfeas.1).div_const (1 - p)
      have hm_d : Measurable (fun t => 1 / D_ext β (y_fn hs p t) - 1 / (1 + β)) :=
        (continuous_const.div ((continuous_D_ext β).comp hcont_y)
          fun t => (D_ext_pos hβ _).ne').measurable.sub measurable_const
      exact (hm_sp.mul hm_d).ennreal_ofReal.aemeasurable
    rw [← lintegral_add_left' hm1]
    refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    have hsp_nn : 0 ≤ survProb p q t / (1 - p) :=
      div_nonneg (survProb_nonneg hfeas.1 ht) h1mp.le
    have hdiff_nn : 0 ≤ 1 / D_ext β (y_fn hs p t) - 1 / (1 + β) := by
      have hle := D_ext_le β (y_fn hs p t)
      have hpos := D_ext_pos hβ (y_fn hs p t)
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hpos hle)
    rw [← ENNReal.ofReal_add (mul_nonneg hsp_nn hdiff_nn) (mul_nonneg hsp_nn (by positivity))]
    congr 1
    have hDne : D_ext β (y_fn hs p t) ≠ 0 := (D_ext_pos hβ _).ne'
    have h1bne : (1 + β) ≠ 0 := by positivity
    field_simp [h1mp.ne', hDne, h1bne]
    ring
  rw [hLHS_eq, hRHS_sub, lintegral_W_identity hs hp hfeas.1] at hcomb
  have hWp_pos : 0 < W_fn hs p p := W_fn_p_pos hs p
  have hreal : α * (1 + β) * W_fn hs p p ≤ W_fn hs p p :=
    (ENNReal.ofReal_le_ofReal_iff hWp_pos.le).mp hcomb
  have hαb : α * (1 + β) ≤ 1 := by nlinarith
  rw [h1b] at hαb
  have h1 : α / s ≤ 1 := by simpa [div_eq_mul_inv] using hαb
  exact (div_le_one hs.1).mp h1

lemma zero_isSDFeasible {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IsSDFeasible p (fun _ _ => 0) 0 := by
  refine ⟨⟨?_, ?_, ?_⟩, le_rfl, zero_le_one, ?_⟩
  · intro _ _ _ _; exact le_rfl
  · intro _ _; exact integrableOn_zero
  · intro t _ _ _
    simp [cumMass]
  · intro k hk
    have h1mp : 0 < 1 - p ^ k := sub_pos.mpr (pow_lt_one₀ hp.1.le hp.2 (by omega))
    have hFk0 : Fk p (fun _ _ => 0) k = 0 := by simp [Fk]
    rw [hFk0, zero_div]

end SampleDrivenOS.Limit.UpperBoundProof

theorem solution (p s : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (hs : IsAlphaStar s) :
    sdclpValue p ≤ s := by
  unfold sdclpValue
  refine csSup_le ⟨0, fun _ _ => 0, SampleDrivenOS.Limit.UpperBoundProof.zero_isSDFeasible hp⟩ ?_
  rintro α ⟨q, hfeas⟩
  exact SampleDrivenOS.Limit.UpperBoundProof.alpha_le_alphaStar hp hs hfeas
