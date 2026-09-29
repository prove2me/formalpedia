-- Prove2me | solution 1 for SparseApprox.Greedy.norm_le_pinv_Abar
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:48:17.827983+00:00
-- url     : https://prove2.me/submissions/5bb14962-6f0e-44a5-818d-a39ca26f82a3

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

lemma aux_npA_norm_normalize {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) (hv : v ≠ 0) :
    ‖normalizeVec v‖ = 1 := by
  unfold normalizeVec
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma aux_npA_inj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ (colE A)) (y : Fin n → ℝ)
    (hy : ∑ i, y i • normalizeVec (colE A i) = 0) : y = 0 := by
  have h := Fintype.linearIndependent_iff.mp hA (fun i => y i * ‖colE A i‖⁻¹) (by
    rw [← hy]; refine Finset.sum_congr rfl fun i _ => ?_
    unfold normalizeVec; rw [smul_smul])
  funext i
  have hi := h i
  have hne : ‖colE A i‖ ≠ 0 := norm_ne_zero_iff.mpr (hA.ne_zero i)
  rcases mul_eq_zero.mp hi with h1 | h1
  · exact h1
  · exact absurd (inv_eq_zero.mp h1) hne

lemma aux_npA_lower {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ (colE A))
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose (Abar A) P)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖y‖ ≤ opNorm2 P * ‖∑ i, y i • normalizeVec (colE A i)‖ := by
  have hL : ∀ z : EuclideanSpace ℝ (Fin n),
      Matrix.toEuclideanLin (Abar A) z = ∑ i, z i • normalizeVec (colE A i) := by
    intro z
    ext j
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Abar, colsMatrix, mul_comm]
  have hinj : ∀ z : EuclideanSpace ℝ (Fin n), Matrix.toEuclideanLin (Abar A) z = 0 → z = 0 := by
    intro z hz
    rw [hL] at hz
    have := aux_npA_inj A hA (fun i => z i) hz
    ext i; exact congrFun this i
  have hQ : Matrix.toEuclideanLin P (Matrix.toEuclideanLin (Abar A) y) = y := by
    have h1 : Matrix.toEuclideanLin (Abar A)
        (Matrix.toEuclideanLin P (Matrix.toEuclideanLin (Abar A) y)) =
        Matrix.toEuclideanLin (Abar A) y := by
      rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
      simp only [WithLp.ofLp_toLp]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP.1]
    have := hinj (Matrix.toEuclideanLin P (Matrix.toEuclideanLin (Abar A) y) - y)
      (by rw [map_sub, h1, sub_self])
    exact sub_eq_zero.mp this
  calc ‖y‖ = ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin P)
        (Matrix.toEuclideanLin (Abar A) y)‖ := by
        rw [LinearMap.coe_toContinuousLinearMap', hQ]
    _ ≤ opNorm2 P * ‖Matrix.toEuclideanLin (Abar A) y‖ := ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hL]

def aux_npA_Inv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s : State m n) : Prop :=
  (∀ j ∉ s.chosen, ‖s.col j‖ = 1) ∧
  (∀ i ∈ s.chosen, ∀ j ∉ s.chosen, ⟪s.col i, s.col j⟫_ℝ = 0) ∧
  (∀ i ∈ s.chosen, ⟪s.col i, s.res⟫_ℝ = 0) ∧
  (∀ x : Fin n → ℝ, (∀ i ∈ s.chosen, x i = 0) →
    ∃ y : Fin n → ℝ, ∑ i, x i • s.col i = ∑ i, y i • normalizeVec (colE A i) ∧
      ∀ i ∉ s.chosen, |x i| ≤ |y i|)

lemma aux_npA_init {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (hA : LinearIndependent ℝ (colE A)) : aux_npA_Inv A (initState A b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j _
    exact aux_npA_norm_normalize _ (hA.ne_zero j)
  · intro i hi; simp [initState] at hi
  · intro i hi; simp [initState] at hi
  · intro x _
    exact ⟨x, rfl, fun i _ => le_refl _⟩

lemma aux_npA_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearIndependent ℝ (colE A)) (s : State m n) (k : Fin n)
    (hk : k ∉ s.chosen) (hs : aux_npA_Inv A s) : aux_npA_Inv A (greedyStep s k) := by
  obtain ⟨hU, hO, hR, hM⟩ := hs
  have hν_le : ∀ j ∉ insert k s.chosen,
      ‖s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k‖ ≤ 1 := by
    intro j hj
    have hjτ : j ∉ s.chosen := fun h => hj (Finset.mem_insert_of_mem h)
    have h1 := hU j hjτ
    have h2 := hU k hk
    have hsq : ‖s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k‖ ^ 2 = 1 - ⟪s.col k, s.col j⟫_ℝ ^ 2 := by
      rw [@norm_sub_sq_real, norm_smul, h1, h2, inner_smul_right, real_inner_comm]
      simp only [Real.norm_eq_abs, mul_one, sq_abs]; ring
    nlinarith [sq_nonneg ⟪s.col k, s.col j⟫_ℝ, norm_nonneg (s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k)]
  have hν_ne : ∀ j ∉ insert k s.chosen, s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k ≠ 0 := by
    intro j hj h0
    have hjτ : j ∉ s.chosen := fun h => hj (Finset.mem_insert_of_mem h)
    have hjk : j ≠ k := fun h => hj (by rw [h]; exact Finset.mem_insert_self _ _)
    obtain ⟨y, hy, hyb⟩ := hM (fun i => (if i = j then 1 else 0) -
        (if i = k then ⟪s.col k, s.col j⟫_ℝ else 0)) (by
      intro i hi
      have h1 : i ≠ j := fun h => hjτ (h ▸ hi)
      have h2 : i ≠ k := fun h => hk (h ▸ hi)
      simp [h1, h2])
    have hsum : ∑ i, ((if i = j then (1:ℝ) else 0) -
        (if i = k then ⟪s.col k, s.col j⟫_ℝ else 0)) • s.col i =
        s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k := by
      simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [hsum, h0] at hy
    have := aux_npA_inj A hA y hy.symm
    have h1 := hyb j hjτ
    norm_num [this, hjk] at h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [greedyStep] at hj ⊢
    rw [if_neg hj]
    exact aux_npA_norm_normalize _ (hν_ne j hj)
  · intro i hi j hj
    simp only [greedyStep] at hi hj ⊢
    rw [if_pos hi, if_neg hj]
    have hjτ : j ∉ s.chosen := fun h => hj (Finset.mem_insert_of_mem h)
    unfold normalizeVec
    rw [inner_smul_right, inner_sub_right, inner_smul_right]
    rcases Finset.mem_insert.mp hi with h | hiτ
    · rw [h, real_inner_self_eq_norm_sq, hU k hk]; ring
    · rw [hO i hiτ j hjτ, hO i hiτ k hk]; ring
  · intro i hi
    simp only [greedyStep] at hi ⊢
    rw [if_pos hi, inner_sub_right, inner_smul_right]
    rcases Finset.mem_insert.mp hi with h | hiτ
    · rw [h, real_inner_self_eq_norm_sq, hU k hk]; ring
    · rw [hR i hiτ, hO i hiτ k hk]; ring
  · intro x hx
    simp only [greedyStep] at hx ⊢
    let z : Fin n → ℝ := fun j => if j ∈ insert k s.chosen then 0 else
      x j * ‖s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k‖⁻¹
    let S : ℝ := ∑ j, z j * ⟪s.col k, s.col j⟫_ℝ
    let x' : Fin n → ℝ := fun i => z i - if i = k then S else 0
    obtain ⟨y, hy, hyb⟩ := hM x' (by
      intro i hi
      have hik : i ≠ k := fun h => hk (h ▸ hi)
      simp [x', z, hi, hik])
    refine ⟨y, ?_, ?_⟩
    · rw [← hy]
      have e1 : ∑ i, x' i • s.col i = ∑ i, z i • s.col i - S • s.col k := by
        simp [x', sub_smul, Finset.sum_sub_distrib, ite_smul]
      have e2 : ∑ i, x i • (if i ∈ insert k s.chosen then s.col i else
          normalizeVec (s.col i - ⟪s.col k, s.col i⟫_ℝ • s.col k)) =
          ∑ i, z i • (s.col i - ⟪s.col k, s.col i⟫_ℝ • s.col k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i ∈ insert k s.chosen
        · simp [z, hi, hx i hi]
        · simp only [z, if_neg hi, normalizeVec, smul_smul]
      rw [e1, e2]
      simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, S, Finset.sum_smul]
    · intro i hi
      have hiτ : i ∉ s.chosen := fun h => hi (Finset.mem_insert_of_mem h)
      have hik : i ≠ k := fun h => hi (by rw [h]; exact Finset.mem_insert_self _ _)
      have h1 := hyb i hiτ
      have hx'i : x' i = x i * ‖s.col i - ⟪s.col k, s.col i⟫_ℝ • s.col k‖⁻¹ := by
        simp [x', z, hi, hik, hiτ]
      rw [hx'i] at h1
      refine le_trans ?_ h1
      rw [abs_mul, abs_inv, abs_norm]
      have hpos : 0 < ‖s.col i - ⟪s.col k, s.col i⟫_ℝ • s.col k‖ :=
        norm_pos_iff.mpr (hν_ne i hi)
      have hle := hν_le i hi
      have h3 : 1 ≤ ‖s.col i - ⟪s.col k, s.col i⟫_ℝ • s.col k‖⁻¹ := (one_le_inv₀ hpos).mpr hle
      exact le_mul_of_one_le_right (abs_nonneg _) h3

lemma aux_npA_inv_all {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (hA : LinearIndependent ℝ (colE A)) (k : ℕ → Fin n) :
    ∀ r, (∀ s < r, k s ∉ (greedyState A b k s).chosen) →
      aux_npA_Inv A (greedyState A b k r) := by
  intro r
  induction r with
  | zero => intro _; exact aux_npA_init A b hA
  | succ r ih =>
    intro h
    exact aux_npA_step A hA _ (k r) (h r (Nat.lt_succ_self r))
      (ih fun s hs => h s (Nat.lt_succ_of_lt hs))

end SparseApprox.Greedy

open SparseApprox.Greedy

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε)
    (hA : LinearIndependent ℝ (colE A))
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose (Abar A) P)
    (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u) :
    ‖u‖ ≤ 3 / 2 * opNorm2 P * ‖(greedyState A b k r).res‖ := by
  have hinv := aux_npA_inv_all A b hA k r (fun s hs => (hrun s (lt_trans hs hr)).2.1)
  have hres : ε < ‖(greedyState A b k r).res‖ := (hrun r hr).1
  obtain ⟨hU, hO, hR, hM⟩ := hinv
  set st := greedyState A b k r with hst
  have hvan : ∀ i ∈ st.chosen, u i = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i0, hi0, hu0⟩ := hcon
    let v : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i => if i ∈ st.chosen then 0 else u i)
    have hvfeas : ‖(∑ i, v i • st.col i) - st.res‖ ≤ ε / 2 := by
      refine le_trans ?_ hu.1
      have hdec : (∑ i, u i • st.col i) - st.res =
          (∑ i, (if i ∈ st.chosen then u i else 0) • st.col i) +
            ((∑ i, v i • st.col i) - st.res) := by
        have : ∀ i, u i • st.col i =
            (if i ∈ st.chosen then u i else 0) • st.col i + v i • st.col i := by
          intro i; by_cases hi : i ∈ st.chosen <;> simp [v, hi]
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]; abel
      have horth : ⟪∑ i, (if i ∈ st.chosen then u i else 0) • st.col i,
          (∑ i, v i • st.col i) - st.res⟫_ℝ = 0 := by
        rw [sum_inner]
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : i ∈ st.chosen
        · rw [inner_smul_left, inner_sub_right, inner_sum, hR i hi]
          rw [Finset.sum_eq_zero (fun j _ => ?_)]
          · simp
          · by_cases hj : j ∈ st.chosen
            · simp [v, hj]
            · rw [inner_smul_right, hO i hi j hj, mul_zero]
        · simp [hi]
      rw [hdec]
      have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      nlinarith [norm_nonneg (∑ i, (if i ∈ st.chosen then u i else 0) • st.col i),
        norm_nonneg ((∑ i, v i • st.col i) - st.res),
        norm_nonneg ((∑ i, (if i ∈ st.chosen then u i else 0) • st.col i) +
            ((∑ i, v i • st.col i) - st.res)),
        mul_self_nonneg ‖∑ i, (if i ∈ st.chosen then u i else 0) • st.col i‖]
    have hcard := hu.2 v hvfeas
    have hsub : nzSet v ⊂ nzSet u := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i0, ?_, ?_⟩
        · simp [nzSet, hu0]
        · simp [nzSet, v, hi0]
      · intro i
        simp only [nzSet, Finset.mem_filter, Finset.mem_univ, true_and, v, PiLp.toLp_apply]
        split_ifs <;> simp_all
    have := Finset.card_lt_card hsub
    unfold nnz at hcard
    omega
  obtain ⟨y, hy, hyb⟩ := hM (fun i => u i) hvan
  have hlow := aux_npA_lower A hA P hP (WithLp.toLp 2 y)
  have huy : ‖u‖ ≤ ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i ∈ st.chosen
    · simp [hvan i hi]; positivity
    · have := hyb i hi
      simp only [Real.norm_eq_abs, sq_abs, PiLp.toLp_apply]
      nlinarith [abs_nonneg (u i), abs_nonneg (y i), sq_abs (u i), sq_abs (y i)]
  have hsumeq : ∑ i, (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n)) i • normalizeVec (colE A i) =
      ∑ i, u i • st.col i := by
    rw [hy]
  rw [hsumeq] at hlow
  have hbd : ‖∑ i, u i • st.col i‖ ≤ 3 / 2 * ‖st.res‖ := by
    calc ‖∑ i, u i • st.col i‖ = ‖(∑ i, u i • st.col i - st.res) + st.res‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖∑ i, u i • st.col i - st.res‖ + ‖st.res‖ := norm_add_le _ _
      _ ≤ ε / 2 + ‖st.res‖ := by linarith [hu.1]
      _ ≤ 3 / 2 * ‖st.res‖ := by linarith
  have hP0 : 0 ≤ opNorm2 P := norm_nonneg _
  calc ‖u‖ ≤ opNorm2 P * ‖∑ i, u i • st.col i‖ := le_trans huy hlow
    _ ≤ opNorm2 P * (3 / 2 * ‖st.res‖) := mul_le_mul_of_nonneg_left hbd hP0
    _ = 3 / 2 * opNorm2 P * ‖st.res‖ := by ring
