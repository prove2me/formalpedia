-- Prove2me | solution 1 for PandoraKnapsack.Skipping.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:04:45.502414+00:00
-- url     : https://prove2.me/submissions/b2464ab0-6d66-4c5e-a344-1fdc6bb7523a

import Theorems.Thm_PandoraKnapsack_Skipping_lemma_B_1

namespace PandoraKnapsack.Skipping

/-- Index of the unique bucket containing the time, including the singleton at zero. -/
private def bucket (t : ℕ) : ℕ := if t = 0 then 0 else blockOf t

private lemma bucket_le (t : ℕ) : bucket t ≤ t := by
  by_cases h : t = 0
  · simp [bucket, h]
  · simpa [bucket, h, blockOf] using Nat.pow_log_le_self 2 h

private lemma bucket_double (t : ℕ) : t ≤ 2 * bucket t := by
  by_cases h : t = 0
  · simp [bucket, h]
  · have := Nat.lt_pow_succ_log_self (b := 2) (by decide) t
    simpa [bucket, h, blockOf, pow_succ, Nat.mul_comm] using this.le

private lemma bucket_mem {t b : ℕ} (h : t ≤ b) : bucket t ∈ breakpoints b := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by have := bucket_le t; omega), ?_⟩
  unfold bucket
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

private lemma bucket_mono : Monotone bucket := by
  intro a b hab
  by_cases ha : a = 0
  · simp [bucket, ha]
  have hb : b ≠ 0 := by omega
  simp only [bucket, if_neg ha, if_neg hb, blockOf]
  exact Nat.pow_le_pow_right (by decide) (Nat.log_mono_right hab)

private lemma bucket_zero_iff (t : ℕ) : bucket t = 0 ↔ t = 0 := by
  by_cases h : t = 0 <;> simp [bucket, blockOf, h]

private lemma bucket_fiber {b r : ℕ} (hr : r ∈ breakpoints b) (hpos : r ≠ 0) :
    (Finset.range (b+1)).filter (fun t => bucket t = r) = blockInterval b r := by
  classical
  obtain ⟨hrb, hre⟩ := Finset.mem_filter.mp hr
  obtain ⟨l,rfl⟩ := hre.resolve_left hpos
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, blockInterval, Finset.mem_Ico]
  constructor
  · rintro ⟨htb, h⟩
    have ht : t ≠ 0 := by rintro rfl; exact hpos (by simpa [bucket] using h.symm)
    have h1 := bucket_le t
    have h2 := Nat.lt_pow_succ_log_self (b := 2) (by decide) t
    change _ < 2 ^ (Nat.log 2 t + 1) at h2
    rw [pow_succ] at h2
    have he : 2 ^ Nat.log 2 t = 2 ^ l := by simpa [bucket, ht, blockOf] using h
    rw [h] at h1
    rw [he] at h2
    omega
  · rintro ⟨⟨h1,h2⟩,hb⟩
    have ht : t ≠ 0 := by omega
    have he := Nat.log_eq_of_pow_le_of_lt_pow h1 (by simpa [pow_succ, Nat.mul_comm] using h2)
    exact ⟨by omega, by simp [bucket, ht, blockOf, he]⟩

variable {n m T : ℕ}

private lemma lift_fiber_mass (b : ℕ) (x : LPArray n m) (i : Fin n) (j : Fin m)
    {r : ℕ} (hr : r ∈ breakpoints b) :
    ∑ t ∈ (Finset.range (b+1)).filter (fun t => bucket t = r), liftY b x i j t = x i j r := by
  classical
  by_cases hz : r = 0
  · subst r
    simp [bucket_zero_iff, liftY]
  have hb := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  have hrI : r ∈ blockInterval b r := by
    simp only [blockInterval, Finset.mem_filter, Finset.mem_Ico]
    omega
  have hc : ((blockInterval b r).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨_,hrI⟩).ne'
  calc
    _ = ∑ _t ∈ (Finset.range (b+1)).filter (fun t => bucket t = r),
          x i j r / ((blockInterval b r).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨htb, htr⟩ := Finset.mem_filter.mp ht
      have htb' := Finset.mem_range.mp htb
      have ht0 : t ≠ 0 := by rintro rfl; simp [bucket] at htr; omega
      have hblock : blockOf t = r := by simpa [bucket, ht0] using htr
      simp [liftY, ht0, show t ≤ b by omega, hblock]
    _ = _ := by
      rw [bucket_fiber hr hz]
      simp [nsmul_eq_mul]
      field_simp

private lemma lift_regroup (b : ℕ) (x : LPArray n m) (i : Fin n) (j : Fin m) (w : ℕ → ℝ) :
    ∑ t ∈ Finset.range (b+1), w (bucket t) * liftY b x i j t =
      ∑ r ∈ breakpoints b, w r * x i j r := by
  classical
  calc
    _ = ∑ t ∈ Finset.range (b+1), ∑ r ∈ breakpoints b,
          if bucket t = r then w r * liftY b x i j t else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      have hm := bucket_mem (b := b) (t := t) (by simpa using ht)
      simp [hm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.sum_filter, ← Finset.mul_sum, lift_fiber_mass b x i j hr]

private lemma lift_box {I : Instance n m T} {b : ℕ} {x : LPArray n m} (hx : PsiPFeasible I b x)
    (i : Fin n) (j : Fin m) {t : ℕ} (ht : t ≤ b) :
    0 ≤ liftY b x i j t ∧ liftY b x i j t ≤ 1 := by
  have h := hx.2.2 i j _ (bucket_mem ht)
  by_cases hz : t = 0
  · simpa [liftY, hz, bucket] using h
  simp only [bucket, if_neg hz] at h
  have h1 := bucket_le t
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by decide) t
  rw [pow_succ] at h2
  have hm : t ∈ blockInterval b (blockOf t) := by
    simp only [blockInterval, Finset.mem_filter, Finset.mem_Ico]
    rw [bucket, if_neg hz] at h1
    exact ⟨⟨h1, by simpa [blockOf,mul_comm] using h2⟩,ht⟩
  have hc : 1 ≤ ((blockInterval b (blockOf t)).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨_,hm⟩)
  rw [liftY, if_neg hz, if_pos ht]
  exact ⟨div_nonneg h.1 (by linarith), (div_le_one (by linarith)).mpr (h.2.trans hc)⟩

private lemma lift_prefix {I : Instance n m T} {b : ℕ} {x : LPArray n m}
    (hx : PsiPFeasible I b x) (i : Fin n) (j : Fin m) {t : ℕ} (ht : t ≤ b) :
    ∑ u ∈ Finset.range (t+1), liftY b x i j u ≤
      ∑ r ∈ (breakpoints b).filter (· ≤ bucket t), x i j r := by
  classical
  have he := lift_regroup b x i j (fun r => if r ≤ bucket t then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter] at he
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    have := Finset.mem_range.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),bucket_mono (by omega)⟩
  · intro u hu _
    exact (lift_box hx i j (by simpa using (Finset.mem_filter.mp hu).1)).1

private lemma lift_feasible {I : Instance n m T} {b : ℕ} {x : LPArray n m}
    (hx : PsiPFeasible I b x) : PsiFeasible I b (liftY b x) := by
  refine ⟨?_, ?_, fun i j t ht => lift_box hx i j ht⟩
  · intro t ht
    calc
      _ ≤ ∑ i, ∑ j, ∑ r ∈ (breakpoints b).filter (· ≤ bucket t),
            x i j r * mu I i j (2 * bucket t) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simp only [← Finset.sum_mul]
        have hm : mu I i j t ≤ mu I i j (2 * bucket t) := by
          unfold mu truncMean
          apply Finset.sum_le_sum
          intro s _
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          apply min_le_min_left
          exact_mod_cast bucket_double t
        apply mul_le_mul (lift_prefix hx i j ht) hm
        · unfold mu truncMean
          positivity
        · apply Finset.sum_nonneg
          intro r hr
          exact (hx.2.2 i j _ (Finset.mem_filter.mp hr).1).1
      _ ≤ 2 * (bucket t : ℝ) := hx.1 _ (bucket_mem ht)
      _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_left 2 (bucket_le t)
  · intro i
    convert hx.2.1 i using 1
    apply Finset.sum_congr rfl
    intro j _
    simpa using lift_regroup b x i j (fun _ => 1)

private lemma earlier_weight (I : Instance n m T) (hI : IsValid I) (i : Fin n) (j : Fin m)
    {u t : ℕ} (h : u ≤ t) : effWeight I i j t ≤ effWeight I i j u := by
  have hc : 0 ≤ cdf I i j ((T : ℝ) - (0 : ℕ)) := by
    unfold cdf
    positivity
  have hv : 0 ≤ I.value i := by
    by_contra! hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg hn.le hc
    have hp := hI.2.2 i j
    unfold effWeight at hp
    linarith [hI.2.1 i j]
  unfold effWeight
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ hv
  unfold cdf
  apply Finset.sum_le_sum
  intro s hs
  have h' : (u : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
  split_ifs <;> first | rfl | positivity | linarith

private lemma lift_objective (I : Instance n m T) (hI : IsValid I) (b : ℕ)
    (x : LPArray n m) (hx : PsiPFeasible I b x) :
    psiPObjective I b x ≤ psiObjective I b (liftY b x) := by
  unfold psiPObjective psiObjective
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [← lift_regroup b x i j (fun r => effWeight I i j (2*r))]
  apply Finset.sum_le_sum
  intro t ht
  apply mul_le_mul_of_nonneg_right (earlier_weight I hI i j (bucket_double t))
  exact (lift_box hx i j (by simpa using ht)).1

end PandoraKnapsack.Skipping

open PandoraKnapsack.Skipping

theorem solution {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (b : ℕ)
    (xStar : LPArray n m) (hx : PsiPOptimal I b xStar) :
    PsiFeasible I b (liftY b xStar) ∧
      ∀ x : LPArray n m, PsiFeasible I b x →
        psiObjective I b x / 4 ≤ psiObjective I b (liftY b xStar) := by
  refine ⟨lift_feasible hx.1, ?_⟩
  intro x h
  obtain ⟨z,hz,hval⟩ := lemma_B_1 I hI b x h
  exact hval.trans ((hx.2 z hz).trans (lift_objective I hI b xStar hx.1))
