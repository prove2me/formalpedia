-- Prove2me | solution 1 for PandoraKnapsack.Skipping.dyadic_sparse_half
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:14:58.561636+00:00
-- url     : https://prove2.me/submissions/8795cee3-eae0-4f36-9907-478c28378146

import Definitions.Def_PandoraKnapsack_Skipping_CompactLP

namespace PandoraKnapsack.Skipping


private def bucket (t : ℕ) := if t = 0 then 0 else 2 ^ Nat.log 2 t

private lemma bucket_le (t : ℕ) : bucket t ≤ t := by
  unfold bucket
  split_ifs with h
  · omega
  · exact Nat.pow_log_le_self 2 h

private lemma time_le_double_bucket (t : ℕ) : t ≤ 2 * bucket t := by
  unfold bucket
  split_ifs with h
  · omega
  · have hlog := Nat.lt_pow_succ_log_self (b := 2) (by decide) t
    rw [pow_succ] at hlog
    omega

private lemma bucket_break {t b : ℕ} (h : t ≤ b) : bucket t ∈ breakpoints b := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by have := bucket_le t; omega), ?_⟩
  unfold bucket
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

private lemma bucket_range {t b : ℕ} (h : t ≤ b) : bucket t ∈ Finset.range (b+1) :=
  Finset.mem_range.mpr (by have := bucket_le t; omega)

private noncomputable def compress {n m : ℕ} (b : ℕ) (x : LPArray n m) : LPArray n m :=
  fun i j r => (∑ t ∈ Finset.range (b + 1), if bucket t = r then x i j t else 0) / 2

variable {n m T : ℕ}

private lemma compress_item {I : Instance n m T} {b : ℕ} {x : LPArray n m}
    (hx : PsiFeasible I b x) (i : Fin n) :
    ∑ j, ∑ r ∈ Finset.range (b+1), compress b x i j r ≤ 1 := by
  classical
  have regroup (j : Fin m) :
      ∑ r ∈ Finset.range (b+1), compress b x i j r =
        (∑ t ∈ Finset.range (b+1), x i j t) / 2 := by
    unfold compress
    rw [← Finset.sum_div, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    have hm := bucket_range (b := b) (t := t) (by simpa using ht)
    simp [hm]
  simp_rw [regroup]
  rw [← Finset.sum_div]
  linarith [hx.2.1 i]

private lemma compress_box {I : Instance n m T} {b : ℕ} {x : LPArray n m}
    (hx : PsiFeasible I b x) (i : Fin n) (j : Fin m) (r : ℕ) (hr : r ∈ Finset.range (b+1)) :
    0 ≤ compress b x i j r ∧ compress b x i j r ≤ 1 := by
  have nn (k : Fin m) (s : ℕ) : 0 ≤ compress b x i k s := by
    unfold compress
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro t ht
    split_ifs
    · exact (hx.2.2 i k t (by simpa using ht)).1
    · exact le_rfl
  refine ⟨nn j r, ?_⟩
  calc
    compress b x i j r ≤ ∑ s ∈ Finset.range (b+1), compress b x i j s :=
      Finset.single_le_sum (fun s _ => nn j s) hr
    _ ≤ ∑ k, ∑ s ∈ Finset.range (b+1), compress b x i k s :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun s _ => nn k s)) (Finset.mem_univ j)
    _ ≤ 1 := compress_item hx i


private lemma compressed_prefix {b r : ℕ} (I : Instance n m T) (x : LPArray n m)
    (hx : PsiFeasible I b x) (i : Fin n) (j : Fin m) :
    ∑ u ∈ Finset.range (r+1), compress b x i j u ≤
      (∑ t ∈ Finset.range (min b (2*r) + 1), x i j t) / 2 := by
  classical
  unfold compress
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [Finset.sum_ite_eq]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨hb, hs⟩ := Finset.mem_filter.mp ht
    simp only [Finset.mem_range] at hb hs ⊢
    have := time_le_double_bucket t
    omega
  · intro t ht _
    have := Finset.mem_range.mp ht
    exact (hx.2.2 i j t (by omega)).1

private lemma compress_capacity (I : Instance n m T) (b : ℕ) (x : LPArray n m)
    (hx : PsiFeasible I b x) (r : ℕ) (hr : r ≤ b) :
    ∑ i, ∑ j, ∑ u ∈ Finset.range (r+1), compress b x i j u * mu I i j r ≤ 2 * (r : ℝ) := by
  let c := min b (2*r)
  have hcb : c ≤ b := min_le_left ..
  have hrc : r ≤ c := le_min hr (by omega)
  have hc2 : c ≤ 2*r := min_le_right ..
  calc
    _ ≤ ∑ i, ∑ j, (∑ t ∈ Finset.range (c+1), x i j t * mu I i j c) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hm : 0 ≤ mu I i j r := by unfold mu truncMean; positivity
      have ha : 0 ≤ ∑ t ∈ Finset.range (c+1), x i j t := Finset.sum_nonneg fun t ht =>
        (hx.2.2 i j t (by have := Finset.mem_range.mp ht; omega)).1
      have hmu : mu I i j r ≤ mu I i j c := by
        unfold mu truncMean
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (min_le_min_left _ (by exact_mod_cast hrc)) ENNReal.toReal_nonneg
      calc
        _ ≤ ((∑ t ∈ Finset.range (c+1), x i j t)/2) * mu I i j r :=
          mul_le_mul_of_nonneg_right (compressed_prefix I x hx i j) hm
        _ ≤ ((∑ t ∈ Finset.range (c+1), x i j t)/2) * mu I i j c :=
          mul_le_mul_of_nonneg_left hmu (by positivity)
        _ = _ := by ring
    _ = (∑ i, ∑ j, ∑ t ∈ Finset.range (c+1), x i j t * mu I i j c) / 2 := by
      simp only [Finset.sum_div]
    _ ≤ _ := by
      have := hx.1 c hcb
      have : (c : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hc2
      linarith
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

private lemma compress_objective (I : Instance n m T) (hI : IsValid I) (b : ℕ)
    (x : LPArray n m) (hx : PsiFeasible I b x) :
    psiObjective I b x / 2 ≤ psiObjective I b (compress b x) := by
  classical
  unfold psiObjective
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  simp only [Finset.sum_mul, compress, mul_div_assoc', div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t ht
  have htb : t ≤ b := by simpa using Finset.mem_range.mp ht
  have hm := bucket_range htb
  simp_rw [mul_ite, mul_zero]
  simp [hm, eq_comm (a := bucket t)]
  exact mul_le_mul_of_nonneg_right (earlier_weight I hI i j (bucket_le t)) (hx.2.2 i j t htb).1


end PandoraKnapsack.Skipping

open PandoraKnapsack.Skipping

theorem solution {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (b : ℕ)
    (x : LPArray n m) (hx : PsiFeasible I b x) :
    ∃ y : LPArray n m, PsiFeasible I b y ∧
      (∀ i j t, t ∉ breakpoints b → y i j t = 0) ∧
      psiObjective I b x / 2 ≤ psiObjective I b y := by
  refine ⟨compress b x, ⟨compress_capacity I b x hx, compress_item hx,
    fun i j r hr => compress_box hx i j r (by simpa using hr)⟩, ?_, compress_objective I hI b x hx⟩
  intro i j t ht
  unfold compress
  rw [Finset.sum_eq_zero, zero_div]
  intro u hu
  have : bucket u ≠ t := fun h => ht (h ▸ bucket_break (b := b) (t := u) (by simpa using hu))
  simp [this]
