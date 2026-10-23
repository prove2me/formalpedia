-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.averageChannelTypical
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:45:28.079591+00:00
-- url     : https://prove2.me/submissions/13a66d3b-5243-4119-92c2-acc0c90c3f86

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

theorem g79c_expY {n d : ℕ} (q : Fin n → Fin d → ℝ) (hq1 : ∀ k, ∑ j, q k j = 1)
    (T : Finset (Fin n)) (j : Fin d) :
    ∑ v : Fin n → Fin d, (∏ k, q k (v k)) * (if ∀ i ∈ T, v i = j then (1:ℝ) else 0)
      = ∏ i ∈ T, q i j := by
  have key : ∀ v : Fin n → Fin d, (∏ k, q k (v k)) * (if ∀ i ∈ T, v i = j then (1:ℝ) else 0)
      = ∏ k, (q k (v k) * (if k ∈ T ∧ v k ≠ j then 0 else 1)) := by
    intro v
    rw [Finset.prod_mul_distrib]
    congr 1
    split_ifs with h
    · symm; apply Finset.prod_eq_one; intro i _
      rw [if_neg]; push_neg; exact fun hi => h i hi
    · push_neg at h; obtain ⟨i, hi, hne⟩ := h
      symm; apply Finset.prod_eq_zero (Finset.mem_univ i); simp [hi, hne]
  simp_rw [key]
  rw [← Fintype.prod_sum (fun k c => q k c * if k ∈ T ∧ c ≠ j then (0:ℝ) else 1)]
  have hf : ∀ k, ∑ c, q k c * (if k ∈ T ∧ c ≠ j then (0:ℝ) else 1) = if k ∈ T then q k j else 1 := by
    intro k
    by_cases hk : k ∈ T
    · simp [hk]
    · simp [hk, hq1]
  simp_rw [hf]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem g79c_var {n d : ℕ} (q : Fin n → Fin d → ℝ) (hq1 : ∀ k, ∑ j, q k j = 1) (j : Fin d) :
    ∑ v : Fin n → Fin d, (∏ k, q k (v k)) * ((count v j : ℝ) - ∑ k, q k j) ^ 2
      = ∑ k, (q k j - q k j ^ 2) := by
  set X : Fin n → (Fin n → Fin d) → ℝ := fun k v => if v k = j then 1 else 0 with hX
  have hc : ∀ v : Fin n → Fin d, (count v j : ℝ) - ∑ k, q k j = ∑ k, (X k v - q k j) := by
    intro v
    rw [Finset.sum_sub_distrib]
    simp only [count, hX]
    rw [Finset.natCast_card_filter]
  have h2 : ∀ k l, ∑ v : Fin n → Fin d, (∏ i, q i (v i)) * ((X k v - q k j) * (X l v - q l j))
      = if k = l then q k j - q k j ^ 2 else 0 := by
    intro k l
    have e1 : ∀ v : Fin n → Fin d, X k v * X l v = if ∀ i ∈ ({k, l} : Finset (Fin n)), v i = j then 1 else 0 := by
      intro v; simp only [hX, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      split_ifs <;> simp_all
    have Ek : ∀ k, ∑ v : Fin n → Fin d, (∏ i, q i (v i)) * X k v = q k j := by
      intro k; have := g79c_expY q hq1 {k} j; simpa [hX] using this
    have E0 : ∑ v : Fin n → Fin d, (∏ i, q i (v i)) * 1 = 1 := by
      have := g79c_expY q hq1 ∅ j; simpa using this
    have Ekl : ∑ v : Fin n → Fin d, (∏ i, q i (v i)) * (X k v * X l v) = ∏ i ∈ ({k, l} : Finset (Fin n)), q i j := by
      simp_rw [e1]; exact g79c_expY q hq1 _ j
    have expand : ∀ v : Fin n → Fin d, (∏ i, q i (v i)) * ((X k v - q k j) * (X l v - q l j))
        = (∏ i, q i (v i)) * (X k v * X l v) - q l j * ((∏ i, q i (v i)) * X k v)
          - q k j * ((∏ i, q i (v i)) * X l v) + q k j * q l j * ((∏ i, q i (v i)) * 1) := by
      intro v; ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, Ekl, Ek, Ek, E0]
    by_cases hkl : k = l
    · subst hkl; simp; ring
    · simp [hkl]; ring
  simp_rw [hc, sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine (Finset.sum_comm.trans (Finset.sum_congr rfl fun k _ => Finset.sum_comm)).trans ?_
  simp_rw [h2]
  simp [sq]

theorem g79c_bad {n d : ℕ} (q : Fin n → Fin d → ℝ) (hq0 : ∀ k j, 0 ≤ q k j)
    (hq1 : ∀ k, ∑ j, q k j = 1) (p : Fin d → ℝ) (hp : ∀ j, ∑ k, q k j = n * p j)
    (A : ℝ) (hA : 0 < A) (j : Fin d) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d =>
      ¬ |(count v j : ℝ) - n * p j| ≤ A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n),
      ∏ k, q k (v k) ≤ 1 / A ^ 2 := by
  set t := A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n with ht
  have ht0 : 0 ≤ t := by positivity
  have hπ0 : ∀ v : Fin n → Fin d, 0 ≤ ∏ k, q k (v k) := fun v => Finset.prod_nonneg fun k _ => hq0 _ _
  have hvar := g79c_var q hq1 j
  rw [hp j] at hvar
  set Var := ∑ v : Fin n → Fin d, (∏ k, q k (v k)) * ((count v j : ℝ) - n * p j) ^ 2 with hVar
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun k => q k j)
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  rw [hp j] at hcs
  have hsq : ∑ k, (q k j - q k j ^ 2) = n * p j - ∑ k, q k j ^ 2 := by
    rw [Finset.sum_sub_distrib, hp j]
  have hVle : (n:ℝ) * Var ≤ (n:ℝ) * (n * (p j * (1 - p j))) := by
    rw [hvar, hsq]; nlinarith
  have hVnn : 0 ≤ Var := Finset.sum_nonneg fun v _ => mul_nonneg (hπ0 v) (sq_nonneg _)
  have hBadle : ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d =>
      ¬ |(count v j : ℝ) - n * p j| ≤ t), (∏ k, q k (v k)) * t ^ 2 ≤ Var := by
    calc _ ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d =>
      ¬ |(count v j : ℝ) - n * p j| ≤ t), (∏ k, q k (v k)) * ((count v j : ℝ) - n * p j) ^ 2 := by
          apply Finset.sum_le_sum; intro v hv
          simp only [Finset.mem_filter, not_le] at hv
          apply mul_le_mul_of_nonneg_left _ (hπ0 v)
          rw [← sq_abs ((count v j : ℝ) - n * p j)]
          nlinarith [hv.2]
      _ ≤ Var := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun v _ _ => mul_nonneg (hπ0 v) (sq_nonneg _))
  rw [← Finset.sum_mul] at hBadle
  by_cases hpos : 0 < (n:ℝ) * (p j * (1 - p j))
  · have hn : 0 < (n:ℝ) := by
      rcases (Nat.cast_nonneg n : (0:ℝ) ≤ n).lt_or_eq with h | h
      · exact h
      · rw [← h] at hpos; simp at hpos
    have hs : 0 < p j * (1 - p j) := by
      by_contra h; push_neg at h; nlinarith
    have ht2 : t ^ 2 = A ^ 2 * (n * (p j * (1 - p j))) := by
      rw [ht, mul_pow, mul_pow, Real.sq_sqrt hs.le, Real.sq_sqrt hn.le]; ring
    have hV : Var ≤ n * (p j * (1 - p j)) := le_of_mul_le_mul_left hVle hn
    rw [ht2] at hBadle
    rw [le_div_iff₀ (by positivity)]
    have := hBadle.trans hV
    by_contra hc
    have hc' := lt_of_not_ge hc
    nlinarith [mul_lt_mul_of_pos_right hc' hpos]
  · push_neg at hpos
    have hV0 : Var = 0 := by
      rcases (Nat.cast_nonneg n : (0:ℝ) ≤ n).lt_or_eq with h | h
      · have := le_of_mul_le_mul_left hVle h; linarith
      · rw [hVar]
        have hn0 : n = 0 := by exact_mod_cast h.symm
        subst hn0
        apply Finset.sum_eq_zero; intro v _
        have : (count v j : ℝ) = 0 := by simp [count]
        simp [this]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => mul_nonneg (hπ0 v) (sq_nonneg _))).1 hV0
    have : ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d =>
      ¬ |(count v j : ℝ) - n * p j| ≤ t), ∏ k, q k (v k) = 0 := by
      apply Finset.sum_eq_zero; intro v hv
      simp only [Finset.mem_filter, not_le] at hv
      have h1 := hall v (Finset.mem_univ v)
      have h2 : 0 < ((count v j : ℝ) - n * p j) ^ 2 := by
        rw [← sq_abs]; exact pow_pos (lt_of_le_of_lt ht0 hv.2) 2
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h h2.ne'
    rw [this]; positivity

theorem g79c_prob {n d : ℕ} (q : Fin n → Fin d → ℝ) (hq0 : ∀ k j, 0 ≤ q k j)
    (hq1 : ∀ k, ∑ j, q k j = 1) (p : Fin d → ℝ) (hp : ∀ j, ∑ k, q k j = n * p j)
    (A : ℝ) (hA : 0 < A) :
    1 - d / A ^ 2 ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d => ∀ j,
      |(count v j : ℝ) - n * p j| ≤ A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n),
      ∏ k, q k (v k) := by
  have hπ0 : ∀ v : Fin n → Fin d, 0 ≤ ∏ k, q k (v k) := fun v => Finset.prod_nonneg fun k _ => hq0 _ _
  have htot : ∑ v : Fin n → Fin d, ∏ k, q k (v k) = 1 := by
    rw [← Fintype.prod_sum (fun k c => q k c)]; simp [hq1]
  set good := Finset.univ.filter (fun v : Fin n → Fin d => ∀ j,
      |(count v j : ℝ) - n * p j| ≤ A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n → Fin d))
    (fun v : Fin n → Fin d => ∀ j,
      |(count v j : ℝ) - n * p j| ≤ A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n)
    (fun v => ∏ k, q k (v k))
  rw [htot] at hsplit
  have hrest : ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d => ¬ ∀ j,
      |(count v j : ℝ) - n * p j| ≤ A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n), ∏ k, q k (v k)
      ≤ ∑ j : Fin d, ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d =>
      ¬ |(count v j : ℝ) - n * p j| ≤ A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n),
      ∏ k, q k (v k) := by
    have hpt : ∀ v : Fin n → Fin d, (if ¬ ∀ j,
        |(count v j : ℝ) - n * p j| ≤ A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n
        then ∏ k, q k (v k) else 0) ≤ ∑ j : Fin d, (if ¬ |(count v j : ℝ) - n * p j| ≤
        A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n then ∏ k, q k (v k) else 0) := by
      intro v
      by_cases h : ∀ j, |(count v j : ℝ) - n * p j| ≤ A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n
      · rw [if_neg (not_not.2 h)]
        exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hπ0 v]
      · rw [if_pos h]
        push_neg at h; obtain ⟨j, hj⟩ := h
        have := Finset.single_le_sum (f := fun j => if ¬ |(count v j : ℝ) - n * p j| ≤
          A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n then ∏ k, q k (v k) else 0)
          (fun j _ => by split_ifs <;> simp [hπ0 v]) (Finset.mem_univ j)
        simpa [not_le.2 hj] using this
    rw [Finset.sum_filter]
    refine (Finset.sum_le_sum fun v _ => hpt v).trans (le_of_eq ?_)
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_filter]
  have hb : ∑ j : Fin d, ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d =>
      ¬ |(count v j : ℝ) - n * p j| ≤ A * Real.sqrt (p j * (1 - p j)) * Real.sqrt n),
      ∏ k, q k (v k) ≤ ∑ j : Fin d, 1 / A ^ 2 :=
    Finset.sum_le_sum fun j _ => g79c_bad q hq0 hq1 p hp A hA j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  rw [mul_one_div] at hb
  linarith
theorem g79c_trace_wt {n d : ℕ} (A B : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    (wordTensor A * wordTensor B).trace = ∏ k, (A k * B k).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, wordTensor]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.prod_mul_distrib]

theorem g79c_atom_trace {d : ℕ} (S : FineResolution d) (W : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    (W * S.atom j).trace = ((S.basis : Matrix (Fin d) (Fin d) ℂ)ᴴ * W * (S.basis : Matrix (Fin d) (Fin d) ℂ)) j j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, FineResolution.atom, Matrix.conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [RCLike.star_def]; ring

theorem g79c_atom_sum {d : ℕ} (S : FineResolution d) : ∑ j, S.atom j = 1 := by
  have hU := (Matrix.mem_unitaryGroup_iff).1 S.basis.2
  ext a b
  rw [← hU]
  simp [Matrix.sum_apply, FineResolution.atom, Matrix.mul_apply, Matrix.star_apply, RCLike.star_def]

theorem g79c_avg_trace {d : ℕ} (S : FineResolution d) (j : Fin d) :
    (S.state * S.atom j).trace = (S.weight j : ℂ) := by
  have hU := (Matrix.mem_unitaryGroup_iff').1 S.basis.2
  rw [g79c_atom_trace]
  simp only [FineResolution.state, QAlgorithms.Papers.Independent.Dependency50.P19.Spectrum.density, QAlgorithms.conjSuperop]
  set U : Matrix (Fin d) (Fin d) ℂ := (S.basis : Matrix (Fin d) (Fin d) ℂ)
  have hU' : Uᴴ * U = 1 := hU
  have : Uᴴ * (U * Matrix.diagonal (fun x => (S.weight x : ℂ)) * Uᴴ) * U = Matrix.diagonal (fun x => (S.weight x : ℂ)) := by
    rw [show Uᴴ * (U * Matrix.diagonal (fun x => (S.weight x : ℂ)) * Uᴴ) * U
      = (Uᴴ * U) * Matrix.diagonal (fun x => (S.weight x : ℂ)) * (Uᴴ * U) by simp only [Matrix.mul_assoc]]
    rw [hU']; simp
  rw [this]; simp

/-- Lemma II.11, PDF pp.29-30. No commutativity is assumed among the channel states;
only the average state's own fine spectral resolution is chosen. -/
theorem solution {a d n : ℕ} (ha : 0 < a) (hn : 0 < n)
    (W : Fin a → Matrix (Fin d) (Fin d) ℂ) (hW : ∀ x, IsDensityMatrix (W x))
    (w : Fin n → Fin a) (average : FineResolution d)
    (haverage : average.state = ∑ x, (empiricalWeight w x : ℂ) • W x)
    (delta : ℝ) (hdelta : 0 < delta) :
    effectProb (wordTensor (fun k => W (w k))) (varianceProjector average n (delta * Real.sqrt a)) ≥
      1 - (a : ℝ) * d / delta^2 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (average.basis : Matrix (Fin d) (Fin d) ℂ) with hU
  set q : Fin n → Fin d → ℝ := fun k j => ((Uᴴ * W (w k) * U) j j).re with hqdef
  have hqC : ∀ x j, (W x * average.atom j).trace = (((Uᴴ * W x * U) j j).re : ℂ) := by
    intro x j
    rw [g79c_atom_trace]
    have hM := ((hW x).1.conjTranspose_mul_mul_same U).diag_nonneg (i := j)
    have him := (Complex.nonneg_iff.1 hM).2
    rw [← hU]
    apply Complex.ext <;> simp [← him]
  have hq0 : ∀ k j, 0 ≤ q k j := by
    intro k j
    have hM := ((hW (w k)).1.conjTranspose_mul_mul_same U).diag_nonneg (i := j)
    exact (Complex.nonneg_iff.1 hM).1
  have hq1 : ∀ k, ∑ j, q k j = 1 := by
    intro k
    have h1 : ∑ j, (W (w k) * average.atom j).trace = 1 := by
      rw [← Matrix.trace_sum, ← Finset.mul_sum, g79c_atom_sum, Matrix.mul_one]
      exact (hW (w k)).2
    simp_rw [hqC] at h1
    have := congrArg Complex.re h1
    simpa [hqdef] using this
  have hlaw : ∀ j, (average.law j).toReal = average.weight j := by
    intro j
    simp [FineResolution.law, ENNReal.toReal_ofReal (average.nonneg j)]
  have hp : ∀ j, ∑ k, q k j = n * (average.law j).toReal := by
    intro j
    rw [hlaw]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h1 := g79c_avg_trace average j
    rw [haverage, Finset.sum_mul, Matrix.trace_sum] at h1
    simp_rw [Matrix.smul_mul, Matrix.trace_smul, hqC, smul_eq_mul] at h1
    have h2 : ∑ k, q k j = ∑ x, (count w x : ℝ) * ((Uᴴ * W x * U) j j).re := by
      simp only [hqdef, count]
      simp_rw [Finset.natCast_card_filter, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp
    rw [h2]
    have h3 := congrArg Complex.re h1
    simp only [Complex.re_sum, empiricalWeight] at h3
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re] at h3
    rw [← h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    field_simp
  have hA : 0 < delta * Real.sqrt a := by
    have : (0:ℝ) < a := by exact_mod_cast ha
    positivity
  have key := g79c_prob q hq0 hq1 (fun j => (average.law j).toReal) hp _ hA
  have heq : effectProb (wordTensor (fun k => W (w k))) (varianceProjector average n (delta * Real.sqrt a))
      = ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d => ∀ j,
      |(count v j : ℝ) - n * (average.law j).toReal| ≤ (delta * Real.sqrt a) *
        Real.sqrt ((average.law j).toReal * (1 - (average.law j).toReal)) * Real.sqrt n),
      ∏ k, q k (v k) := by
    simp only [effectProb, varianceProjector, varianceSet, Matrix.mul_sum, Matrix.trace_sum,
      g79c_trace_wt, hqC, Complex.re_sum]
    refine Finset.sum_congr (by ext v; simp) fun v _ => ?_
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  rw [heq, ge_iff_le]
  refine le_trans ?_ key
  have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have : (d:ℝ) / (delta ^ 2 * a) ≤ a * d / delta ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0:ℝ) ≤ d := by positivity
    nlinarith [mul_nonneg this (sq_nonneg delta), mul_nonneg (mul_nonneg this (sq_nonneg delta)) (by linarith : (0:ℝ) ≤ a - 1)]
  linarith



end
