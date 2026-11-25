-- Prove2me | solution 1 for PandoraKnapsack.Skipping.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T16:50:06.867+00:00
-- url     : https://prove2.me/submissions/16e0095f-d11c-43bb-b754-8c955e1941b5

import Definitions.Def_PandoraKnapsack_Skipping_CompactLP

namespace PandoraKnapsack.Skipping

/-- Assign a start to the largest dyadic breakpoint whose double is at most the start.
The two earliest starts both go to breakpoint zero. -/
private def roundTime (t : ℕ) : ℕ :=
  if t < 2 then 0 else 2 ^ Nat.log 2 (t / 2)

private lemma twice_round_le (t : ℕ) : 2 * roundTime t ≤ t := by
  unfold roundTime
  split_ifs with h
  · omega
  · have := Nat.pow_log_le_self 2 (x := t / 2) (by omega)
    omega

private lemma round_mem {t b : ℕ} (h : t ≤ b) : roundTime t ∈ breakpoints b := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by have := twice_round_le t; omega), ?_⟩
  unfold roundTime
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

private lemma before_cut {t r : ℕ} (hr : 0 < r) (h : roundTime t ≤ r) : t ≤ 4 * r := by
  unfold roundTime at h
  split_ifs at h with ht
  · omega
  · have hlog := Nat.lt_pow_succ_log_self (b := 2) (by decide) (t / 2)
    rw [pow_succ] at hlog
    omega

/-- Aggregate each time bucket and retain one quarter of its mass. -/
private noncomputable def compress {n m : ℕ} (b : ℕ) (x : LPArray n m) : LPArray n m :=
  fun i j r => (∑ t ∈ Finset.range (b + 1), if roundTime t = r then x i j t else 0) / 4

variable {n m T : ℕ}

private lemma compress_item {I : Instance n m T} {b : ℕ} {x : LPArray n m}
    (hx : PsiFeasible I b x) (i : Fin n) :
    ∑ j, ∑ r ∈ breakpoints b, compress b x i j r ≤ 1 := by
  classical
  have regroup (j : Fin m) :
      ∑ r ∈ breakpoints b, compress b x i j r =
        (∑ t ∈ Finset.range (b+1), x i j t) / 4 := by
    unfold compress
    rw [← Finset.sum_div, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    have hm := round_mem (b := b) (t := t) (by simpa using ht)
    simp [hm]
  simp_rw [regroup]
  rw [← Finset.sum_div]
  linarith [hx.2.1 i]

private lemma compress_box {I : Instance n m T} {b : ℕ} {x : LPArray n m}
    (hx : PsiFeasible I b x) (i : Fin n) (j : Fin m) (r : ℕ) (hr : r ∈ breakpoints b) :
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
    compress b x i j r ≤ ∑ s ∈ breakpoints b, compress b x i j s :=
      Finset.single_le_sum (fun s _ => nn j s) hr
    _ ≤ ∑ k, ∑ s ∈ breakpoints b, compress b x i k s :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun s _ => nn k s)) (Finset.mem_univ j)
    _ ≤ 1 := compress_item hx i

private lemma compressed_prefix {b r : ℕ} (hr : 0 < r) (I : Instance n m T) (x : LPArray n m)
    (hx : PsiFeasible I b x) (i : Fin n) (j : Fin m) :
    ∑ u ∈ (breakpoints b).filter (· ≤ r), compress b x i j u ≤
      (∑ t ∈ Finset.range (min b (4*r) + 1), x i j t) / 4 := by
  classical
  unfold compress
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [Finset.sum_ite_eq]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨hb, hs⟩ := Finset.mem_filter.mp ht
    obtain ⟨_, hur⟩ := Finset.mem_filter.mp hs
    simp only [Finset.mem_range] at hb ⊢
    have := before_cut hr hur
    omega
  · intro t ht _
    have := Finset.mem_range.mp ht
    exact (hx.2.2 i j t (by omega)).1

private lemma mu_scaled (I : Instance n m T) (i : Fin n) (j : Fin m) {d c : ℕ}
    {k : ℝ} (hk : 1 ≤ k) (hd : (d : ℝ) ≤ (c : ℝ) * k) :
    mu I i j d ≤ mu I i j c * k := by
  unfold mu truncMean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  rcases le_total (s.val : ℝ) c with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (le_mul_of_one_le_right (by positivity) hk)
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans hd

private lemma compress_capacity {n m T : ℕ} (I : Instance n m T) (b : ℕ) (x : LPArray n m)
    (hx : PsiFeasible I b x) :
    ∀ r ∈ breakpoints b, ∑ i, ∑ j, ∑ u ∈ (breakpoints b).filter (· ≤ r),
      compress b x i j u * mu I i j (2*r) ≤ 2 * (r : ℝ) := by
  classical
  intro r hr
  by_cases hz : r = 0
  · subst r
    simp [mu, truncMean]
  have hpos : 0 < r := Nat.pos_of_ne_zero hz
  let c := min b (4*r)
  have hcb : c ≤ b := min_le_left .. 
  have hrc : r ≤ c := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    dsimp [c]
    omega
  obtain ⟨k, hk, hd, hlim⟩ : ∃ k : ℝ, 1 ≤ k ∧ ((2*r : ℕ) : ℝ) ≤ (c : ℝ)*k ∧
      (c : ℝ)*k ≤ 4 * (r : ℝ) := by
    have hc4 : c ≤ 4*r := min_le_right .. 
    by_cases h : 2*r ≤ c
    · refine ⟨1, le_rfl, ?_, ?_⟩ <;> simp only [mul_one] <;> exact_mod_cast (by omega : _)
    · refine ⟨2, by norm_num, ?_, ?_⟩ <;> push_cast <;> linarith only [show (r : ℝ) ≤ c by exact_mod_cast hrc,
          show (c : ℝ) ≤ 2*r by exact_mod_cast (by omega : c ≤ 2*r)]
  have hglobal := hx.1 c hcb
  calc
    _ ≤ ∑ i, ∑ j, (∑ t ∈ Finset.range (c+1), x i j t * mu I i j c) * (k/4) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hm : 0 ≤ mu I i j (2*r) := by unfold mu truncMean; positivity
      have ha : 0 ≤ ∑ t ∈ Finset.range (c+1), x i j t := Finset.sum_nonneg fun t ht =>
        (hx.2.2 i j t (by have := Finset.mem_range.mp ht; omega)).1
      have hprefix := compressed_prefix hpos I x hx i j
      calc
        _ ≤ ((∑ t ∈ Finset.range (c+1), x i j t)/4) * mu I i j (2*r) :=
          mul_le_mul_of_nonneg_right hprefix hm
        _ ≤ ((∑ t ∈ Finset.range (c+1), x i j t)/4) * (mu I i j c * k) :=
          mul_le_mul_of_nonneg_left (mu_scaled I i j hk hd) (by positivity)
        _ = _ := by ring
    _ = (∑ i, ∑ j, ∑ t ∈ Finset.range (c+1), x i j t * mu I i j c) * (k/4) := by
      simp only [Finset.sum_mul]
    _ ≤ 2 * (c : ℝ) * (k/4) := mul_le_mul_of_nonneg_right hglobal (by linarith)
    _ ≤ _ := by linarith

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
    psiObjective I b x / 4 ≤ psiPObjective I b (compress b x) := by
  classical
  unfold psiObjective psiPObjective
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
  simp only [Finset.sum_mul, compress, mul_div_assoc', div_mul_cancel₀ _ (by norm_num : (4:ℝ) ≠ 0)]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t ht
  have htb : t ≤ b := by simpa using Finset.mem_range.mp ht
  have hm := round_mem htb
  simp_rw [mul_ite, mul_zero]
  simp [hm, eq_comm (a := roundTime t)]
  exact mul_le_mul_of_nonneg_right (earlier_weight I hI i j (twice_round_le t)) (hx.2.2 i j t htb).1

end PandoraKnapsack.Skipping

open PandoraKnapsack.Skipping

theorem solution {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (b : ℕ) (x : LPArray n m)
    (hx : PsiFeasible I b x) :
    ∃ xHat : LPArray n m, PsiPFeasible I b xHat ∧
      psiObjective I b x / 4 ≤ psiPObjective I b xHat := by
  exact ⟨compress b x, ⟨compress_capacity I b x hx, compress_item hx, compress_box hx⟩,
    compress_objective I hI b x hx⟩
