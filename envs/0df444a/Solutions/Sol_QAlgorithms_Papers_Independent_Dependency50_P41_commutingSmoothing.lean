-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P41.commutingSmoothing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:00:47.007907+00:00
-- url     : https://prove2.me/submissions/058fc215-9088-456a-a67d-d1b1b6c08b44

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_classicalConditionalH0
noncomputable section

section cs204lib
open scoped Matrix ComplexOrder MatrixOrder

lemma cs204_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma cs204_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma cs204_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma cs204_traceNorm_herm {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]


lemma cs204_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma cs204_tr_psd_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have hs : (cfc Real.sqrt A).IsHermitian := by
    have : (cfc Real.sqrt A).PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]; exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
    exact this.1
  rw [← cs204_sqrt_sq hA, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h := hB.conjTranspose_mul_mul_same (cfc Real.sqrt A)
  rw [hs.eq] at h
  have := h.trace_nonneg
  rw [← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.1 this).1

lemma cs204_tr_le_traceNorm {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) (h1 : (1 - X).PosSemidef) (h2 : (1 + X).PosSemidef) :
    (X * Y).trace.re ≤ QAlgorithms.traceNorm Y := by
  rw [cs204_traceNorm_herm hY]
  set P := cfc (fun t : ℝ => max t 0) Y
  set Q := cfc (fun t : ℝ => max (-t) 0) Y
  have hP : P.PosSemidef := cs204_cfc_psd Y _ (fun t => le_max_right _ _)
  have hQ : Q.PosSemidef := cs204_cfc_psd Y _ (fun t => le_max_right _ _)
  have hYPQ : Y = P - Q := (cs204_parts Y hY).symm
  have a1 := cs204_tr_psd_mul h1 hP
  have a2 := cs204_tr_psd_mul h2 hQ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at a1
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, Complex.add_re] at a2
  rw [hYPQ, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith
lemma cs204_tn_psd {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.PosSemidef) : QAlgorithms.traceNorm X = X.trace.re := by
  rw [cs204_traceNorm_herm hX.1, cs204_cfc_trace hX.1, cs204_cfc_trace hX.1,
    hX.1.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := hX.eigenvalues_nonneg i
  rw [max_eq_left h, max_eq_right (by linarith)]
  simp

def cs204_cj {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (d : n → ℝ) :
    Matrix n n ℂ :=
  U * Matrix.diagonal (fun i => (d i : ℂ)) * star U

lemma cs204_cj_mul {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : star U * U = 1) (d e : n → ℝ) :
    cs204_cj U d * cs204_cj U e = cs204_cj U (fun i => d i * e i) := by
  unfold cs204_cj
  calc U * Matrix.diagonal (fun i => (d i : ℂ)) * star U *
        (U * Matrix.diagonal (fun i => (e i : ℂ)) * star U)
      = U * Matrix.diagonal (fun i => (d i : ℂ)) * (star U * U) *
          Matrix.diagonal (fun i => (e i : ℂ)) * star U := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hU, Matrix.mul_one, Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
      simp

lemma cs204_cj_sub {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (d e : n → ℝ) :
    cs204_cj U d - cs204_cj U e = cs204_cj U (fun i => d i - e i) := by
  unfold cs204_cj
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  simp

lemma cs204_cj_one {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U * star U = 1) : cs204_cj U (fun _ => 1) = 1 := by
  unfold cs204_cj
  simp [hU]

lemma cs204_cj_zero {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) :
    cs204_cj U (fun _ => 0) = 0 := by
  unfold cs204_cj
  simp

lemma cs204_cj_psd {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i) : (cs204_cj U d).PosSemidef := by
  unfold cs204_cj
  rw [Matrix.star_eq_conjTranspose]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast hd i

lemma cs204_cj_trace {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : star U * U = 1) (d : n → ℝ) : (cs204_cj U d).trace = ∑ i, (d i : ℂ) := by
  unfold cs204_cj
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

lemma cs204_cj_rank {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (d : n → ℝ)
    (S : Finset n) (hS : ∀ i, d i ≠ 0 → i ∈ S) : (cs204_cj U d).rank ≤ S.card := by
  unfold cs204_cj
  calc _ ≤ (U * Matrix.diagonal (fun i => (d i : ℂ))).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (Matrix.diagonal (fun i => (d i : ℂ))).rank := Matrix.rank_mul_le_right _ _
    _ = Fintype.card {i // (d i : ℂ) ≠ 0} := Matrix.rank_diagonal _
    _ ≤ S.card := by
      rw [Fintype.card_subtype]
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Complex.ofReal_eq_zero] at hi
      exact hS i hi

lemma cs204_spec {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.IsHermitian) : M = cs204_cj (hM.eigenvectorUnitary : Matrix n n ℂ) hM.eigenvalues := by
  have h := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

lemma cs204_top {ι : Type*} [Fintype ι] [DecidableEq ι] (l : ι → ℝ) :
    ∀ r ≤ Fintype.card ι, ∃ S : Finset ι, S.card = r ∧ ∀ i ∉ S, ∀ j ∈ S, l i ≤ l j := by
  intro r
  induction r with
  | zero => intro _; exact ⟨∅, by simp, by simp⟩
  | succ r ih =>
    intro hr
    obtain ⟨S, hS, hS'⟩ := ih (by omega)
    have hne : (Finset.univ.filter (· ∉ S)).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
      have : Finset.univ ⊆ S := fun x _ => by simpa using h (Finset.mem_univ x)
      have := Finset.card_le_card this
      simp at this
      omega
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image _ l hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨insert j S, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hj, hS]
    · intro i hi k hk
      rw [Finset.mem_insert] at hi hk
      push Not at hi
      rcases hk with rfl | hk
      · exact hjmax i (by simp [hi.2])
      · exact hS' i hi.2 k hk

lemma cs204_thresh {ι : Type*} [Fintype ι] (l : ι → ℝ) (hl : ∀ i, 0 ≤ l i) (S : Finset ι)
    (hS' : ∀ i ∉ S, ∀ j ∈ S, l i ≤ l j) :
    ∃ t, 0 ≤ t ∧ (∀ i ∈ S, t ≤ l i) ∧ ∀ i ∉ S, l i ≤ t := by
  classical
  by_cases h : ∃ i, i ∉ S
  · obtain ⟨i0, hi0⟩ := h
    have hne : (Finset.univ.filter (· ∉ S)).Nonempty := ⟨i0, by simp [hi0]⟩
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ l hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact ⟨l m, hl m, fun j hj => hS' m hm j hj, fun i hi => hmax i (by simp [hi])⟩
  · push Not at h
    exact ⟨0, le_refl _, fun i _ => hl i, fun i hi => absurd (h i) hi⟩

lemma cs204_rearr {ι : Type*} [Fintype ι] [DecidableEq ι] (l w : ι → ℝ) (S : Finset ι) (t : ℝ)
    (ht0 : 0 ≤ t) (hS : ∀ i ∈ S, t ≤ l i) (hSc : ∀ i ∉ S, l i ≤ t)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hsum : ∑ i, (if i ∈ S then (0:ℝ) else 1) ≤ ∑ i, w i) :
    ∑ i, (if i ∈ S then 0 else l i) ≤ ∑ i, w i * l i := by
  have key : ∀ i, (if i ∈ S then 0 else l i) - w i * l i ≤
      t * ((if i ∈ S then 0 else 1) - w i) := by
    intro i
    by_cases h : i ∈ S
    · simp only [h, if_true]; nlinarith [hS i h, hw0 i]
    · simp only [h, if_false]; nlinarith [hSc i h, hw1 i]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at this
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 hsum)]

lemma cs204_count {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    ∑ i, (if i ∈ S then (0:ℝ) else 1) = (Fintype.card ι : ℝ) - S.card := by
  have : ∀ i, (if i ∈ S then (0:ℝ) else 1) = 1 - (if i ∈ S then 1 else 0) := by
    intro i; split_ifs <;> norm_num
  simp_rw [this]
  rw [Finset.sum_sub_distrib, Finset.sum_boole]
  simp

lemma cs204_block {n : Type*} [Fintype n] [DecidableEq n] (M Pi : Matrix n n ℂ) (r : ℕ)
    (hr : r ≤ Fintype.card n) (hM : M.PosSemidef) (hP0 : Pi.PosSemidef)
    (hP1 : (1 - Pi).PosSemidef) (htr : (Fintype.card n : ℝ) - r ≤ Pi.trace.re) :
    ∃ M' : Matrix n n ℂ, M'.PosSemidef ∧ (M - M').PosSemidef ∧ M' * M = M * M' ∧
      M'.rank ≤ r ∧ (M - M').trace.re ≤ (Pi * M).trace.re := by
  set U := (hM.1.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set l := hM.1.eigenvalues with hldef
  have hU1 : star U * U = 1 := Unitary.star_mul_self_of_mem hM.1.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Unitary.mul_star_self_of_mem hM.1.eigenvectorUnitary.2
  have hMe : M = cs204_cj U l := cs204_spec hM.1
  have hl : ∀ i, 0 ≤ l i := hM.eigenvalues_nonneg
  obtain ⟨S, hSc, hS'⟩ := cs204_top l r hr
  obtain ⟨t, ht0, htS, htSc⟩ := cs204_thresh l hl S hS'
  have hdiff : M - cs204_cj U (fun i => if i ∈ S then l i else 0) =
      cs204_cj U (fun i => if i ∈ S then 0 else l i) := by
    rw [hMe, cs204_cj_sub]
    congr 1; funext i; split_ifs <;> ring
  refine ⟨cs204_cj U (fun i => if i ∈ S then l i else 0), ?_, ?_, ?_, ?_, ?_⟩
  · exact cs204_cj_psd _ _ (fun i => by split_ifs <;> simp [hl i])
  · rw [hdiff]; exact cs204_cj_psd _ _ (fun i => by split_ifs <;> simp [hl i])
  · rw [hMe, cs204_cj_mul hU1, cs204_cj_mul hU1]
    congr 1; funext i; ring
  · rw [← hSc]
    apply cs204_cj_rank
    intro i hi
    by_contra h
    simp [h] at hi
  · set Q := star U * Pi * U with hQ
    have e1 : (M - cs204_cj U (fun i => if i ∈ S then l i else 0)).trace.re =
        ∑ i, (if i ∈ S then 0 else l i) := by
      rw [hdiff, cs204_cj_trace hU1, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    have e2 : (Pi * M).trace.re = ∑ i, (Q i i).re * l i := by
      rw [hMe]
      unfold cs204_cj
      have : (Pi * (U * Matrix.diagonal (fun i => (l i : ℂ)) * star U)).trace =
          (Q * Matrix.diagonal (fun i => (l i : ℂ))).trace := by
        rw [show Pi * (U * Matrix.diagonal (fun i => (l i : ℂ)) * star U) =
          (Pi * U * Matrix.diagonal (fun i => (l i : ℂ))) * star U by
            simp only [Matrix.mul_assoc], Matrix.trace_mul_comm, hQ]
        simp only [Matrix.mul_assoc]
      rw [this, Matrix.trace, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.mul_diagonal]
    have hQ0 : Q.PosSemidef := by
      have := hP0.conjTranspose_mul_mul_same U
      rwa [← Matrix.star_eq_conjTranspose] at this
    have hQ1 : (1 - Q).PosSemidef := by
      have := hP1.conjTranspose_mul_mul_same U
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose,
        hU1] at this
      exact this
    have hw0 : ∀ i, 0 ≤ (Q i i).re := fun i =>
      (Complex.nonneg_iff.mp (hQ0.diag_nonneg (i := i))).1
    have hw1 : ∀ i, (Q i i).re ≤ 1 := by
      intro i
      have h := (Complex.nonneg_iff.mp (hQ1.diag_nonneg (i := i))).1
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at h
      linarith
    have hsum : ∑ i, (if i ∈ S then (0:ℝ) else 1) ≤ ∑ i, (Q i i).re := by
      rw [cs204_count, hSc]
      have : ∑ i, (Q i i).re = Pi.trace.re := by
        rw [← Complex.re_sum]
        change Q.trace.re = _
        rw [hQ, Matrix.trace_mul_cycle, hU2, Matrix.one_mul]
      rw [this]; exact htr
    rw [e1, e2]
    exact cs204_rearr l (fun i => (Q i i).re) S t ht0 htS htSc hw0 hw1 hsum

lemma cs204_kerproj {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n ℂ)
    (hN : N.PosSemidef) :
    ∃ Pi : Matrix n n ℂ, Pi.PosSemidef ∧ (1 - Pi).PosSemidef ∧ Pi * N = 0 ∧
      (Fintype.card n : ℝ) - N.rank ≤ Pi.trace.re ∧ Pi * Pi = Pi := by
  set V := (hN.1.eigenvectorUnitary : Matrix n n ℂ)
  set m := hN.1.eigenvalues with hmdef
  have hV1 : star V * V = 1 := Unitary.star_mul_self_of_mem hN.1.eigenvectorUnitary.2
  have hV2 : V * star V = 1 := Unitary.mul_star_self_of_mem hN.1.eigenvectorUnitary.2
  have hNe : N = cs204_cj V m := cs204_spec hN.1
  have hrank : N.rank = Fintype.card {i // m i ≠ 0} := hN.1.rank_eq_card_non_zero_eigs
  refine ⟨cs204_cj V (fun i => if m i = 0 then 1 else 0), ?_, ?_, ?_, ?_, ?_⟩
  · exact cs204_cj_psd _ _ (fun i => by split_ifs <;> norm_num)
  · rw [← cs204_cj_one hV2, cs204_cj_sub]
    exact cs204_cj_psd _ _ (fun i => by split_ifs <;> norm_num)
  · rw [hNe, cs204_cj_mul hV1, ← cs204_cj_zero V]
    congr 1; funext i; split_ifs with h <;> simp [h]
  · rw [cs204_cj_trace hV1, Complex.re_sum, hrank, Fintype.card_subtype]
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => m i = 0)
    have h3 : ∑ i, ((if m i = 0 then (1:ℝ) else 0 : ℝ) : ℂ).re =
        ((Finset.univ.filter (fun i => m i = 0)).card : ℝ) := by
      simp only [apply_ite (fun x : ℝ => ((x : ℂ)).re), Complex.ofReal_re]
      rw [Finset.sum_boole]
    rw [h3]
    have h4 : ((Finset.univ.filter (fun i => m i = 0)).card : ℝ) +
        ((Finset.univ.filter (fun i => ¬ m i = 0)).card : ℝ) = Fintype.card n := by
      exact_mod_cast h2
    simp only [ne_eq]
    linarith
  · rw [cs204_cj_mul hV1]
    congr 1; funext i; split_ifs <;> norm_num

end cs204lib

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder Kronecker
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

lemma cs204_inner {B K : Type*} [Fintype B] [DecidableEq K] {v : K → EuclideanSpace ℂ B}
    (hv : Orthonormal ℂ v) (k j : K) :
    ∑ c, conj (v k c) * v j c = if k = j then 1 else 0 := by
  have h := orthonormal_iff_ite.mp hv k j
  rw [← h, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [RCLike.inner_apply, mul_comm]

lemma cs204_pd_mul {B K : Type*} [Fintype B] [DecidableEq K] {v : K → EuclideanSpace ℂ B}
    (hv : Orthonormal ℂ v) (k j : K) :
    pureDensity (v k) * pureDensity (v j) = if k = j then pureDensity (v k) else 0 := by
  ext a b
  have h' := cs204_inner hv k j
  have e : (pureDensity (v k) * pureDensity (v j)) a b =
      v k a * conj (v j b) * ∑ c, conj (v k c) * v j c := by
    simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [e, h']
  split_ifs with hkj
  · subst hkj; simp [pureDensity]
  · simp

lemma cs204_pd_trace {B K : Type*} [Fintype B] {v : K → EuclideanSpace ℂ B}
    (hv : Orthonormal ℂ v) (k : K) : (pureDensity (v k)).trace = 1 := by
  classical
  have h' := cs204_inner hv k k
  rw [if_pos rfl] at h'
  rw [← h', Matrix.trace]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [pureDensity, mul_comm]

lemma cs204_pd_psd {B : Type*} [Fintype B] (ψ : EuclideanSpace ℂ B) :
    (pureDensity ψ).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (fun b => ψ b)
  convert h using 1
  ext a b
  simp [pureDensity, Matrix.vecMulVec_apply]

lemma cs204_cq_mul {A B K : Type*} [Fintype A] [Fintype B] [Fintype K]
    {v : K → EuclideanSpace ℂ B} (hv : Orthonormal ℂ v) (X Y : K → Op A) :
    cqOperator v X * cqOperator v Y = cqOperator v (fun k => X k * Y k) := by
  classical
  unfold cqOperator
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmk : ∀ j, Matrix.kronecker (X k) (pureDensity (v k)) *
      Matrix.kronecker (Y j) (pureDensity (v j)) =
      if k = j then Matrix.kronecker (X k * Y k) (pureDensity (v k)) else 0 := by
    intro j
    have e : Matrix.kronecker (X k) (pureDensity (v k)) *
        Matrix.kronecker (Y j) (pureDensity (v j)) =
        Matrix.kronecker (X k * Y j) (pureDensity (v k) * pureDensity (v j)) :=
      (Matrix.mul_kronecker_mul _ _ _ _).symm
    rw [e, cs204_pd_mul hv]
    split_ifs with h
    · subst h; rfl
    · exact Matrix.kronecker_zero _
  rw [Finset.sum_congr rfl fun j _ => hmk j]
  simp

lemma cs204_cq_sub {A B K : Type*} [Fintype K]
    (v : K → EuclideanSpace ℂ B) (f g : K → Op A) :
    cqOperator v f - cqOperator v g = cqOperator v (fun k => f k - g k) := by
  unfold cqOperator
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext x y
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, sub_mul]

lemma cs204_cq_psd {A B K : Type*} [Fintype A] [Fintype B] [Fintype K]
    (v : K → EuclideanSpace ℂ B) (X : K → Op A) (hX : ∀ k, (X k).PosSemidef) :
    (cqOperator v X).PosSemidef :=
  Matrix.posSemidef_sum _ (fun k _ => (hX k).kronecker (cs204_pd_psd _))

lemma cs204_cq_trace {A B K : Type*} [Fintype A] [Fintype B] [Fintype K]
    {v : K → EuclideanSpace ℂ B} (hv : Orthonormal ℂ v) (X : K → Op A) :
    (cqOperator v X).trace = ∑ k, (X k).trace := by
  unfold cqOperator
  rw [Matrix.trace_sum]
  simp [Matrix.trace_kronecker, cs204_pd_trace hv]

lemma cs204_logRank_mono {I : Type*} [Fintype I] {X Y : Op I} (h : X.rank ≤ Y.rank) :
    logRank X ≤ logRank Y := by
  unfold logRank logExtended
  have h' : (X.rank : ℝ) ≤ Y.rank := by exact_mod_cast h
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact bot_le
  · exact absurd (h'.trans h2) h1
  · exact EReal.coe_le_coe_iff.2 (Real.logb_le_logb_of_le (by norm_num) (by linarith) h')

lemma cs204_improve {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v)
    (blocks : K → Op A) (hblocks : ∀ k, (blocks k).PosSemidef) (epsilon : ℝ)
    (σ : Op (A × B)) (hσ : σ ∈ cqBall (cqOperator v blocks) v epsilon) :
    ∃ σ' ∈ {sigma ∈ cqBall (cqOperator v blocks) v epsilon |
        sigma * cqOperator v blocks = cqOperator v blocks * sigma},
      conditionalH0 σ' ≤ conditionalH0 σ := by
  obtain ⟨⟨sb, hsb, rfl⟩, hd⟩ := hσ
  choose Pi hP0 hP1 hPN htr hPP using fun k => cs204_kerproj (sb k) (hsb k)
  choose M' hM'0 hM'1 hcomm hrank htrace using fun k =>
    cs204_block (blocks k) (Pi k) (sb k).rank (Matrix.rank_le_card_width _) (hblocks k)
      (hP0 k) (hP1 k) (htr k)
  refine ⟨cqOperator v M', ⟨⟨⟨M', hM'0, rfl⟩, ?_⟩, ?_⟩, ?_⟩
  · set W := cqOperator v Pi with hWdef
    have hW : W * W = W := by
      rw [hWdef, cs204_cq_mul hv]
      congr 1; funext k; exact hPP k
    have hWh : W.IsHermitian := (cs204_cq_psd v Pi hP0).1
    have h1 : (1 - W).PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self (1 - W)
      have e : (1 - W)ᴴ * (1 - W) = 1 - W := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hWh.eq, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.mul_sub, hW]
        simp
      rwa [e] at this
    have h2 : (1 + W).PosSemidef := Matrix.PosSemidef.one.add (cs204_cq_psd v Pi hP0)
    have hY : (cqOperator v blocks - cqOperator v sb).IsHermitian :=
      (cs204_cq_psd v blocks hblocks).1.sub (cs204_cq_psd v sb hsb).1
    have key := cs204_tr_le_traceNorm hY h1 h2
    have eW : (W * (cqOperator v blocks - cqOperator v sb)).trace.re =
        ∑ k, (Pi k * blocks k).trace.re := by
      rw [cs204_cq_sub, hWdef, cs204_cq_mul hv, cs204_cq_trace hv, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_sub, hPN k, sub_zero]
    have eL : QAlgorithms.traceNorm (cqOperator v blocks - cqOperator v M') =
        ∑ k, (blocks k - M' k).trace.re := by
      rw [cs204_cq_sub, cs204_tn_psd (cs204_cq_psd v _ hM'1), cs204_cq_trace hv, Complex.re_sum]
    calc QAlgorithms.traceNorm (cqOperator v blocks - cqOperator v M')
        = ∑ k, (blocks k - M' k).trace.re := eL
      _ ≤ ∑ k, (Pi k * blocks k).trace.re := Finset.sum_le_sum fun k _ => htrace k
      _ = _ := eW.symm
      _ ≤ _ := key
      _ ≤ epsilon := hd
  · rw [cs204_cq_mul hv, cs204_cq_mul hv]
    congr 1; funext k; exact hcomm k
  · rw [classicalConditionalH0 v hv _ hM'0, classicalConditionalH0 v hv _ hsb]
    exact iSup_mono fun k => cs204_logRank_mono (hrank k)

end QAlgorithms.Papers.Independent.Dependency50.P41

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P41
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped ComplexConjugate Matrix ComplexOrder

/-- arXiv:1108.5357v3, PDF pp.20–21, Lemma 28.
Equality of infima uses the corrected Definition 4, with no trace restriction on smoothing. -/
theorem solution {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v)
    (blocks : K → Op A) (hblocks : ∀ k, (blocks k).PosSemidef)
    (hstate : IsDensityMatrix (cqOperator v blocks))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    smoothH0 (cqOperator v blocks) v epsilon =
      commutingSmoothH0 (cqOperator v blocks) v epsilon := by
  unfold smoothH0 commutingSmoothH0
  apply le_antisymm
  · exact sInf_le_sInf (Set.image_mono fun σ h => h.1)
  · apply le_sInf
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨σ', hσ', hle⟩ := cs204_improve v hv blocks hblocks epsilon σ hσ
    exact (sInf_le (Set.mem_image_of_mem _ hσ')).trans hle

end

