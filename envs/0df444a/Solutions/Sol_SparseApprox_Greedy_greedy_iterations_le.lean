-- Prove2me | solution 1 for SparseApprox.Greedy.greedy_iterations_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:11:09.371212+00:00
-- url     : https://prove2.me/submissions/da8a5b70-baac-4852-98ff-7c46b1f66574

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem aux_gi_norm_normalize_le {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    ‖normalizeVec v‖ ≤ 1 := by
  unfold normalizeVec
  rw [norm_smul]
  by_cases hv : v = 0
  · simp [hv]
  · rw [norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem aux_gi_smul_normalize {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    ‖v‖ • normalizeVec v = v := by
  unfold normalizeVec
  by_cases hv : v = 0
  · simp [hv]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

theorem aux_gi_normalize_smul {m : ℕ} (c : ℝ) (hc : 0 < c) (v : EuclideanSpace ℝ (Fin m)) :
    normalizeVec (c • v) = normalizeVec v := by
  unfold normalizeVec
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
  congr 1
  field_simp

theorem aux_gi_normalize_idem {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    normalizeVec (normalizeVec v) = normalizeVec v := by
  by_cases hv : v = 0
  · simp [hv, normalizeVec]
  · conv_lhs => rw [normalizeVec]
    exact aux_gi_normalize_smul _ (inv_pos.mpr (norm_pos_iff.mpr hv)) v

theorem aux_gi_norm_sub_proj_sq {m : ℕ} (a u : EuclideanSpace ℝ (Fin m)) (ha : ‖a‖ ≤ 1) :
    ‖u - ⟪a, u⟫_ℝ • a‖ ^ 2 ≤ ‖u‖ ^ 2 - ⟪a, u⟫_ℝ ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, real_inner_comm a u, Real.norm_eq_abs,
    mul_pow, sq_abs]
  have h1 : ‖a‖ ^ 2 ≤ 1 := by
    have := norm_nonneg a
    nlinarith
  nlinarith [sq_nonneg ⟪u, a⟫_ℝ]

theorem aux_gi_toE_eq_sum {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin M v = ∑ j, v j • colE M j := by
  ext i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, colE, mul_comm]

theorem aux_gi_colE_colsMatrix {m n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin m)) (j : Fin n) :
    colE (colsMatrix f) j = f j := by
  ext i
  simp [colE, colsMatrix]


/-- The rank-one update `v ↦ Q v - ⟪a, Q v⟫ a`. -/
noncomputable def aux_gi_proj {m : ℕ} (a : EuclideanSpace ℝ (Fin m))
    (Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun v := Q v - ⟪a, Q v⟫_ℝ • a
  map_add' u v := by
    simp only [map_add, inner_add_right, add_smul]
    abel
  map_smul' c v := by
    simp only [map_smul, inner_smul_right, RingHom.id_apply, smul_sub, smul_smul]

theorem aux_gi_proj_apply {m : ℕ} (a : EuclideanSpace ℝ (Fin m))
    (Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin m)) :
    aux_gi_proj a Q v = Q v - ⟪a, Q v⟫_ℝ • a := rfl

/-- Invariant of the greedy iteration. -/
def aux_gi_Inv {m n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin m)) (b : EuclideanSpace ℝ (Fin m))
    (s : State m n) (Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) : Prop :=
  s.res = Q b ∧
  (∀ j ∉ s.chosen, s.col j = normalizeVec (Q (a j))) ∧
  (∀ j ∈ s.chosen, Q (a j) = 0) ∧
  (∀ v, ‖Q v‖ ≤ ‖v‖) ∧
  (∀ v, Q v - v ∈ Submodule.span ℝ (a '' (s.chosen : Set (Fin n))))

theorem aux_gi_Inv_step {m n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (s : State m n)
    (Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (k : Fin n)
    (h : aux_gi_Inv a b s Q) (hk : k ∉ s.chosen) :
    aux_gi_Inv a b (greedyStep s k) (aux_gi_proj (s.col k) Q) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hcolk : s.col k = normalizeVec (Q (a k)) := h2 k hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [greedyStep, aux_gi_proj_apply, h1]
  · intro j hj
    have hj' : j ∉ s.chosen := fun hh => hj (Finset.mem_insert_of_mem hh)
    have hj2 : j ∉ insert k s.chosen := hj
    simp only [greedyStep, aux_gi_proj_apply]
    rw [if_neg hj2]
    have hQ : Q (a j) = ‖Q (a j)‖ • s.col j := by
      rw [h2 j hj', aux_gi_smul_normalize]
    rcases (norm_nonneg (Q (a j))).eq_or_lt with hc | hc
    · have hz : Q (a j) = 0 := norm_eq_zero.mp hc.symm
      have hcj : s.col j = 0 := by rw [h2 j hj', hz]; simp [normalizeVec]
      rw [hz, hcj]
    · conv_rhs => rw [hQ]
      rw [inner_smul_right, mul_smul, ← smul_sub, aux_gi_normalize_smul _ hc]
  · intro j hj
    simp only [greedyStep] at hj
    rw [aux_gi_proj_apply]
    rcases Finset.mem_insert.mp hj with hjk | hjs
    · subst hjk
      rw [hcolk]
      set v := Q (a j)
      by_cases hv : v = 0
      · rw [hv]; simp
      · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        unfold normalizeVec
        rw [inner_smul_left, real_inner_self_eq_norm_sq, smul_smul]
        simp only [conj_trivial]
        rw [show ‖v‖⁻¹ * ‖v‖ ^ 2 * ‖v‖⁻¹ = 1 by field_simp, one_smul, sub_self]
    · rw [h3 j hjs]; simp
  · intro v
    rw [aux_gi_proj_apply]
    have hle := aux_gi_norm_sub_proj_sq (s.col k) (Q v)
      (by rw [hcolk]; exact aux_gi_norm_normalize_le _)
    have h2' : ‖Q v - ⟪s.col k, Q v⟫_ℝ • s.col k‖ ≤ ‖Q v‖ := by
      nlinarith [sq_nonneg ⟪s.col k, Q v⟫_ℝ, norm_nonneg (Q v - ⟪s.col k, Q v⟫_ℝ • s.col k),
        norm_nonneg (Q v)]
    exact h2'.trans (h4 v)
  · intro v
    rw [aux_gi_proj_apply]
    have hsub : Submodule.span ℝ (a '' (s.chosen : Set (Fin n))) ≤
        Submodule.span ℝ (a '' ((greedyStep s k).chosen : Set (Fin n))) := by
      apply Submodule.span_mono
      apply Set.image_mono
      simp [greedyStep]
    have hak : a k ∈ Submodule.span ℝ (a '' ((greedyStep s k).chosen : Set (Fin n))) := by
      apply Submodule.subset_span
      exact ⟨k, by simp [greedyStep], rfl⟩
    have hQak : Q (a k) ∈ Submodule.span ℝ (a '' ((greedyStep s k).chosen : Set (Fin n))) := by
      have := Submodule.add_mem _ (hsub (h5 (a k))) hak
      simpa using this
    have hck : s.col k ∈ Submodule.span ℝ (a '' ((greedyStep s k).chosen : Set (Fin n))) := by
      rw [hcolk]; unfold normalizeVec; exact Submodule.smul_mem _ _ hQak
    rw [sub_right_comm]
    exact Submodule.sub_mem _ (hsub (h5 v)) (Submodule.smul_mem _ _ hck)


theorem aux_gi_key {m n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin m)) (b : EuclideanSpace ℝ (Fin m))
    (s : State m n) (Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (h : aux_gi_Inv a b s Q) (ha : ∀ j, ‖a j‖ ≤ 1) (ε : ℝ) (hε0 : 0 < ε)
    (y : Fin n → ℝ) (hy : ‖(∑ j, y j • a j) - b‖ ≤ ε / 2)
    (S : ℕ) (hS : (Finset.univ.filter (fun j => y j ≠ 0)).card ≤ S)
    (p : ℝ) (hp : ∀ y' : Fin n → ℝ, ∑ j, y' j ^ 2 ≤ p ^ 2 * ‖∑ j, y' j • a j‖ ^ 2)
    (hε : ε < ‖s.res‖) (M : ℝ) (hM : ∀ j ∉ s.chosen, |⟪s.col j, s.res⟫_ℝ| ≤ M) :
    ‖s.res‖ ^ 2 ≤ 9 * S * p ^ 2 * M ^ 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  set B := ‖s.res‖ with hBdef
  have hB : 0 < B := lt_trans hε0 hε
  set u := ∑ j, y j • a j with hu
  set w := Q u with hwdef
  have hw1 : ‖w - s.res‖ ≤ ε / 2 := by
    rw [h1, hwdef, ← map_sub]; exact (h4 _).trans hy
  have hmem := h5 u
  rw [Finsupp.mem_span_image_iff_linearCombination] at hmem
  obtain ⟨l, hl, hlu⟩ := hmem
  rw [Finsupp.mem_supported'] at hl
  have hlu' : Q u - u = ∑ j, l j • a j := by
    rw [← hlu, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  set y' : Fin n → ℝ := fun j => y j + l j with hy'
  have hwy' : w = ∑ j, y' j • a j := by
    simp only [hy', add_smul, Finset.sum_add_distrib]
    rw [← hu, ← hlu', hwdef]; abel
  have hY := hp y'
  rw [← hwy'] at hY
  set z : Fin n → ℝ := fun j => if j ∈ s.chosen then 0 else y j * ‖Q (a j)‖ with hz
  have hwz : w = ∑ j, z j • s.col j := by
    rw [hwdef, hu, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
    by_cases hj : j ∈ s.chosen
    · simp [hz, hj, h3 j hj]
    · simp only [hz, if_neg hj]
      rw [h2 j hj, mul_smul, aux_gi_smul_normalize]
  set supp := Finset.univ.filter (fun j => y j ≠ 0) with hsupp
  set T := ∑ j ∈ supp, |z j| with hT
  have hI : ⟪s.res, w⟫_ℝ = ∑ j, z j * ⟪s.res, s.col j⟫_ℝ := by
    rw [hwz, inner_sum]
    simp [inner_smul_right]
  have hIle : ⟪s.res, w⟫_ℝ ≤ M * T := by
    rw [hI, hT, Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.subset_univ supp)]
    · apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ s.chosen
      · simp [hz, hj]
      · have := hM j hj
        rw [real_inner_comm] at this
        calc z j * ⟪s.res, s.col j⟫_ℝ ≤ |z j * ⟪s.res, s.col j⟫_ℝ| := le_abs_self _
          _ = |z j| * |⟪s.res, s.col j⟫_ℝ| := abs_mul _ _
          _ ≤ |z j| * M := mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ = M * |z j| := mul_comm _ _
    · intro j _ hj
      have hy0 : y j = 0 := by simpa [hsupp] using hj
      simp [hz, hy0]
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hZ : ∑ j, z j ^ 2 ≤ ∑ j, y' j ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ s.chosen
    · simp [hz, hj, sq_nonneg]
    · simp only [hz, hy', if_neg hj, hl j hj, add_zero]
      have hq : ‖Q (a j)‖ ≤ 1 := (h4 _).trans (ha j)
      have hq0 : 0 ≤ ‖Q (a j)‖ := norm_nonneg _
      rw [mul_pow]
      have : ‖Q (a j)‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (y j)]
  have hTsq : T ^ 2 ≤ S * ∑ j, z j ^ 2 := by
    calc T ^ 2 ≤ supp.card * ∑ j ∈ supp, |z j| ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ S * ∑ j, z j ^ 2 := by
        apply mul_le_mul (by exact_mod_cast hS) _ (Finset.sum_nonneg (fun j _ => sq_nonneg _))
          (Nat.cast_nonneg _)
        simp only [sq_abs]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => sq_nonneg _)
  have hw2 : ‖w‖ ≤ B + ε / 2 := by
    have := norm_sub_norm_le w s.res
    linarith
  have hI2 : B ^ 2 - B * (ε / 2) ≤ ⟪s.res, w⟫_ℝ := by
    have e1 : ⟪s.res, w⟫_ℝ = ⟪s.res, s.res⟫_ℝ + ⟪s.res, w - s.res⟫_ℝ := by
      rw [inner_sub_right]; ring
    have e2 := abs_real_inner_le_norm s.res (w - s.res)
    rw [e1, real_inner_self_eq_norm_sq]
    have e3 : -(B * ‖w - s.res‖) ≤ ⟪s.res, w - s.res⟫_ℝ := by
      have := neg_abs_le ⟪s.res, w - s.res⟫_ℝ
      linarith
    have e4 : B * ‖w - s.res‖ ≤ B * (ε / 2) := mul_le_mul_of_nonneg_left hw1 hB.le
    linarith
  have k1 : B ^ 2 / 2 < M * T := by nlinarith
  have k2 : (B ^ 2 / 2) ^ 2 < (M * T) ^ 2 := by
    apply pow_lt_pow_left₀ k1 (by positivity) (by norm_num)
  have k3 : ‖w‖ ^ 2 ≤ (3 * B / 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have k4 : T ^ 2 ≤ S * p ^ 2 * (3 * B / 2) ^ 2 := by
    calc T ^ 2 ≤ S * ∑ j, z j ^ 2 := hTsq
      _ ≤ S * (p ^ 2 * ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left (hZ.trans hY) hS0
      _ ≤ S * (p ^ 2 * (3 * B / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left k3 (sq_nonneg p)) hS0
      _ = S * p ^ 2 * (3 * B / 2) ^ 2 := by ring
  have k5 : (M * T) ^ 2 ≤ M ^ 2 * (S * p ^ 2 * (3 * B / 2) ^ 2) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left k4 (sq_nonneg M)
  have k6 : B ^ 2 * B ^ 2 < B ^ 2 * (9 * S * p ^ 2 * M ^ 2) := by nlinarith
  exact (lt_of_mul_lt_mul_left k6 (sq_nonneg B)).le


theorem aux_gi_Inv_exists {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) :
    ∀ r ≤ t, ∃ Q, aux_gi_Inv (fun j => normalizeVec (colE A j)) b (greedyState A b k r) Q := by
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨LinearMap.id, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · intro j _
      show normalizeVec (colE A j) = normalizeVec (normalizeVec (colE A j))
      rw [aux_gi_normalize_idem]
    · intro j hj
      exact absurd hj (Finset.notMem_empty j)
    · intro v; exact le_rfl
    · intro v; simp
  | succ r ih =>
    intro hr
    obtain ⟨Q, hQ⟩ := ih (Nat.le_of_succ_le hr)
    exact ⟨_, aux_gi_Inv_step _ b _ Q (k r) hQ (hrun r (Nat.lt_of_succ_le hr)).2.1⟩

theorem aux_gi_left_inv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ (colE A))
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose (Abar A) P) (v : Fin n → ℝ) :
    P.mulVec ((Abar A).mulVec v) = v := by
  have hinj : ∀ d : Fin n → ℝ, (Abar A).mulVec d = 0 → d = 0 := by
    intro d hd
    have h1 : Matrix.toEuclideanLin (Abar A) (WithLp.toLp 2 d) = 0 := by
      rw [Matrix.toLpLin_apply]; simp [hd]
    rw [aux_gi_toE_eq_sum] at h1
    simp only [Abar, aux_gi_colE_colsMatrix, normalizeVec, smul_smul] at h1
    have h2 := Fintype.linearIndependent_iff.mp hA _ h1
    funext j
    have h3 := h2 j
    have hc : ‖colE A j‖ ≠ 0 := norm_ne_zero_iff.mpr (hA.ne_zero j)
    simpa [hc] using h3
  have h := hP.1
  have : (Abar A).mulVec (P.mulVec ((Abar A).mulVec v) - v) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h,
      sub_self]
  exact sub_eq_zero.mp (hinj _ this)


theorem aux_gi_main {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε)
    (hA : LinearIndependent ℝ (colE A))
    (hfeas : ∃ x : EuclideanSpace ℝ (Fin n), ‖Matrix.toEuclideanLin A x - b‖ ≤ ε / 2)
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose (Abar A) P)
    (k : ℕ → Fin n) (t : ℕ) (hrun : IsGreedyRun A b ε k t) :
    t ≤ ⌈18 * (optSparsity A b (ε / 2) : ℝ) * opNorm2 P ^ 2 * Real.log (‖b‖ / ε)⌉₊ := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · rw [ht]; exact Nat.zero_le _
  set S := optSparsity A b (ε / 2) with hSdef
  set p := opNorm2 P with hpdef
  set a : Fin n → EuclideanSpace ℝ (Fin m) := fun j => normalizeVec (colE A j) with hadef
  have ha : ∀ j, ‖a j‖ ≤ 1 := fun j => aux_gi_norm_normalize_le _
  -- a sparsest feasible solution
  obtain ⟨x0, hx0⟩ := hfeas
  have hne : {N : ℕ | ∃ x : EuclideanSpace ℝ (Fin n),
      nnz x = N ∧ ‖Matrix.toEuclideanLin A x - b‖ ≤ ε / 2}.Nonempty := ⟨nnz x0, x0, rfl, hx0⟩
  obtain ⟨x, hxn, hxb⟩ := Nat.sInf_mem hne
  change nnz x = S at hxn
  set y : Fin n → ℝ := fun j => ‖colE A j‖ * x j with hydef
  have hyu : ∑ j, y j • a j = Matrix.toEuclideanLin A x := by
    rw [aux_gi_toE_eq_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hc : colE A j = 0
    · simp [hydef, hadef, hc, normalizeVec]
    · have hc' : ‖colE A j‖ ≠ 0 := norm_ne_zero_iff.mpr hc
      simp only [hydef, hadef, normalizeVec, smul_smul]
      congr 1
      field_simp
  have hy : ‖(∑ j, y j • a j) - b‖ ≤ ε / 2 := by rw [hyu]; exact hxb
  have hS : (Finset.univ.filter (fun j => y j ≠ 0)).card ≤ S := by
    rw [← hxn]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hydef] at hj
    simp only [nzSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hx
    exact hj (by rw [hx, mul_zero])
  have hp : ∀ y' : Fin n → ℝ, ∑ j, y' j ^ 2 ≤ p ^ 2 * ‖∑ j, y' j • a j‖ ^ 2 := by
    intro y'
    set v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y' with hv
    have hsum : ∑ j, y' j • a j = Matrix.toEuclideanLin (Abar A) v := by
      rw [aux_gi_toE_eq_sum]
      simp [Abar, aux_gi_colE_colsMatrix, hv, hadef]
    have hinv : Matrix.toEuclideanLin P (Matrix.toEuclideanLin (Abar A) v) = v := by
      rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply]
      rw [WithLp.ofLp_toLp, aux_gi_left_inv A hA P hP]
    have hle : ‖v‖ ≤ p * ‖∑ j, y' j • a j‖ := by
      have := ContinuousLinearMap.le_opNorm
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin P)) (∑ j, y' j • a j)
      rw [LinearMap.coe_toContinuousLinearMap', hsum, hinv] at this
      rw [hsum]; exact this
    have hv2 : ∑ j, y' j ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    rw [hv2, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  -- notation for the run
  set st := greedyState A b k with hst
  have hInv := aux_gi_Inv_exists A b ε k t hrun
  set K : ℝ := 9 * S * p ^ 2 with hK
  have hkey : ∀ r < t, ‖(st r).res‖ ^ 2 ≤
      K * ⟪(st r).col (k r), (st r).res⟫_ℝ ^ 2 := by
    intro r hr
    obtain ⟨Q, hQ⟩ := hInv r hr.le
    have := aux_gi_key a b (st r) Q hQ ha ε hε y hy S hS p hp (hrun r hr).1
      |⟪(st r).col (k r), (st r).res⟫_ℝ| (hrun r hr).2.2.2
    rw [sq_abs] at this
    exact this
  have hdec : ∀ r < t, ‖(st (r + 1)).res‖ ^ 2 ≤
      ‖(st r).res‖ ^ 2 - ⟪(st r).col (k r), (st r).res⟫_ℝ ^ 2 := by
    intro r hr
    obtain ⟨Q, hQ⟩ := hInv r hr.le
    have hcol : ‖(st r).col (k r)‖ ≤ 1 := by
      rw [hQ.2.1 (k r) (hrun r hr).2.1]; exact aux_gi_norm_normalize_le _
    exact aux_gi_norm_sub_proj_sq _ _ hcol
  have hres0 : (st 0).res = b := rfl
  have hb : ε < ‖b‖ := by rw [← hres0]; exact (hrun 0 ht).1
  have hK0 : 0 < K := by
    have h1 := hkey 0 ht
    rw [hres0] at h1
    by_contra hneg
    push Not at hneg
    have : K * ⟪(st 0).col (k 0), (st 0).res⟫_ℝ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg _)
    nlinarith
  have hdecay : ∀ r ≤ t, ‖(st r).res‖ ^ 2 ≤ Real.exp (-(r : ℝ) / K) * ‖b‖ ^ 2 := by
    intro r
    induction r with
    | zero => intro _; simp [hres0]
    | succ r ih =>
      intro hr
      have hr' : r < t := Nat.lt_of_succ_le hr
      have IH := ih hr'.le
      have h1 := hdec r hr'
      have h2 := hkey r hr'
      have hM2 : ‖(st r).res‖ ^ 2 / K ≤ ⟪(st r).col (k r), (st r).res⟫_ℝ ^ 2 := by
        rw [div_le_iff₀ hK0]; linarith
      have hexp : 1 - 1 / K ≤ Real.exp (-1 / K) := by
        have := Real.add_one_le_exp (-1 / K)
        rw [neg_div] at this ⊢
        linarith
      have hsplit : Real.exp (-((r + 1 : ℕ) : ℝ) / K) = Real.exp (-(r : ℝ) / K) * Real.exp (-1 / K) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [hsplit]
      calc ‖(st (r + 1)).res‖ ^ 2 ≤ ‖(st r).res‖ ^ 2 * (1 - 1 / K) := by
            have : ‖(st r).res‖ ^ 2 * (1 - 1 / K) = ‖(st r).res‖ ^ 2 - ‖(st r).res‖ ^ 2 / K := by
              ring
            rw [this]; linarith
        _ ≤ ‖(st r).res‖ ^ 2 * Real.exp (-1 / K) :=
            mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
        _ ≤ (Real.exp (-(r : ℝ) / K) * ‖b‖ ^ 2) * Real.exp (-1 / K) :=
            mul_le_mul_of_nonneg_right IH (Real.exp_pos _).le
        _ = Real.exp (-(r : ℝ) / K) * Real.exp (-1 / K) * ‖b‖ ^ 2 := by ring
  -- final estimate
  set r := t - 1 with hrdef
  have hrt : r < t := by omega
  have hfin := hdecay r hrt.le
  have hεr : ε ^ 2 < ‖(st r).res‖ ^ 2 :=
    pow_lt_pow_left₀ (hrun r hrt).1 hε.le (by norm_num)
  have hbpos : 0 < ‖b‖ := hε.trans hb
  set L := Real.log (‖b‖ / ε) with hL
  have hexpL : Real.exp (2 * L) = ‖b‖ ^ 2 / ε ^ 2 := by
    rw [show 2 * L = L + L by ring, Real.exp_add, hL, Real.exp_log (div_pos hbpos hε)]
    ring
  have hlt : Real.exp ((r : ℝ) / K) < Real.exp (2 * L) := by
    rw [hexpL, lt_div_iff₀ (by positivity)]
    have e1 : Real.exp (-(r : ℝ) / K) * Real.exp ((r : ℝ) / K) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have e2 : ε ^ 2 < Real.exp (-(r : ℝ) / K) * ‖b‖ ^ 2 := hεr.trans_le hfin
    have e3 := mul_lt_mul_of_pos_left e2 (Real.exp_pos ((r : ℝ) / K))
    calc Real.exp (↑r / K) * ε ^ 2 < Real.exp (↑r / K) * (Real.exp (-↑r / K) * ‖b‖ ^ 2) := e3
      _ = (Real.exp (-(r : ℝ) / K) * Real.exp ((r : ℝ) / K)) * ‖b‖ ^ 2 := by ring
      _ = ‖b‖ ^ 2 := by rw [e1, one_mul]
  have hlt2 : (r : ℝ) / K < 2 * L := Real.exp_lt_exp.mp hlt
  have hlt3 : (r : ℝ) < 18 * (S : ℝ) * p ^ 2 * L := by
    rw [div_lt_iff₀ hK0] at hlt2
    rw [hK] at hlt2
    linarith
  have hceil := Nat.le_ceil (18 * (S : ℝ) * p ^ 2 * L)
  have hcast : (r : ℝ) = (t : ℝ) - 1 := by
    rw [hrdef, Nat.cast_sub (by omega)]; simp
  have : (t : ℝ) < (⌈18 * (S : ℝ) * p ^ 2 * L⌉₊ : ℝ) + 1 := by linarith
  have : t < ⌈18 * (S : ℝ) * p ^ 2 * L⌉₊ + 1 := by exact_mod_cast this
  omega

end SparseApprox.Greedy

open SparseApprox.Greedy

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε)
    (hA : LinearIndependent ℝ (colE A))
    (hfeas : ∃ x : EuclideanSpace ℝ (Fin n), ‖Matrix.toEuclideanLin A x - b‖ ≤ ε / 2)
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose (Abar A) P)
    (k : ℕ → Fin n) (t : ℕ) (hrun : IsGreedyRun A b ε k t) :
    t ≤ ⌈18 * (optSparsity A b (ε / 2) : ℝ) * opNorm2 P ^ 2 * Real.log (‖b‖ / ε)⌉₊ :=
  aux_gi_main A b ε hε hA hfeas P hP k t hrun
