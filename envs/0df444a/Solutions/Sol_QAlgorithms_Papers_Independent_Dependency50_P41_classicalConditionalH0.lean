-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P41.classicalConditionalH0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:11:16.718095+00:00
-- url     : https://prove2.me/submissions/dbdcf998-66b6-48e3-af2b-962ecf75af1d

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41
open Matrix
open scoped ComplexConjugate ComplexOrder
open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection) in
lemma X7P41_trace_supp {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (hX : X.IsHermitian) : (supportProjection X).trace = (X.rank : ℂ) := by
  unfold supportProjection
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← mul_assoc]
  rw [show (star (hX.eigenvectorUnitary : Matrix n n ℂ)) * (hX.eigenvectorUnitary : Matrix n n ℂ) = 1
    from Unitary.coe_star_mul_self _]
  rw [one_mul, trace_diagonal, hX.rank_eq_card_non_zero_eigs, Fintype.card_subtype,
    Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : hX.eigenvalues i = 0 <;> simp [h]
lemma X7P41_pd_mul {B : Type} [Fintype B] (x y : EuclideanSpace ℂ B) :
    pureDensity x * pureDensity y = (inner ℂ x y) • Matrix.of (fun a b => x a * conj (y b)) := by
  ext a b
  simp only [pureDensity, mul_apply, of_apply, Matrix.smul_apply, smul_eq_mul,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, RCLike.star_def]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma X7P41_pd_orth {B : Type} {K : Type*} [Fintype B] [DecidableEq K] (v : K → EuclideanSpace ℂ B)
    (hv : Orthonormal ℂ v) (k j : K) :
    pureDensity (v k) * pureDensity (v j) = if k = j then pureDensity (v k) else 0 := by
  rw [X7P41_pd_mul, orthonormal_iff_ite.mp hv]
  split_ifs with h
  · subst h; ext a b; simp [pureDensity]
  · simp

lemma X7P41_pd_herm {B : Type} [Fintype B] (x : EuclideanSpace ℂ B) :
    (pureDensity x).IsHermitian := by
  ext a b; simp [pureDensity, mul_comm]

lemma X7P41_sum_kron {ι : Type*} {m n : Type} (s : Finset ι) (A : ι → Matrix m m ℂ)
    (P : Matrix n n ℂ) :
    kroneckerMap (· * ·) (∑ i ∈ s, A i) P = ∑ i ∈ s, kroneckerMap (· * ·) (A i) P := by
  ext a b; simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

open QAlgorithms.Papers.Independent.Dependency50.P41 in
lemma X7P41_cq_pow {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v) (blocks : K → Matrix A A ℂ) (n : ℕ) :
    (cqOperator v blocks) ^ (n + 1) =
      ∑ k, Matrix.kronecker ((blocks k) ^ (n + 1)) (pureDensity (v k)) := by
  classical
  induction n with
  | zero => simp [cqOperator]
  | succ n ih =>
    rw [pow_succ, ih]
    unfold cqOperator
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    simp only [Matrix.kronecker, ← mul_kronecker_mul, X7P41_pd_orth v hv]
    simp only [apply_ite, kroneckerMap_zero_right (fun x1 x2 : ℂ => x1 * x2) (fun a => mul_zero a)]
    rw [Finset.sum_ite_eq]
    simp [pow_succ]

open QAlgorithms.Papers.Independent.Dependency50.P41 in
lemma X7P41_cq_aeval {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v) (blocks : K → Matrix A A ℂ)
    (p : Polynomial ℝ) (hp : p.eval 0 = 0) :
    Polynomial.aeval (cqOperator v blocks) p =
      ∑ k, Matrix.kronecker (Polynomial.aeval (blocks k) p) (pureDensity (v k)) := by
  have hc : p.coeff 0 = 0 := by rw [Polynomial.coeff_zero_eq_eval_zero, hp]
  simp only [Polynomial.aeval_eq_sum_range]
  simp only [Matrix.kronecker, X7P41_sum_kron, smul_kronecker]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases i with _ | n
  · simp [hc]
  · rw [X7P41_cq_pow v hv blocks n, Finset.smul_sum]
    rfl

open QAlgorithms.Papers.Independent.Dependency50.P41 in
lemma X7P41_cq_herm {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    (v : K → EuclideanSpace ℂ B) (blocks : K → Matrix A A ℂ)
    (hb : ∀ k, (blocks k).IsHermitian) : (cqOperator v blocks).IsHermitian := by
  unfold cqOperator
  simp only [IsHermitian, conjTranspose_sum, Matrix.kronecker, conjTranspose_kronecker]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hb k).eq, (X7P41_pd_herm (v k)).eq]

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection) in
lemma X7P41_supp_eq_aeval {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (hX : X.IsHermitian) (S : Finset ℝ) (hS : ∀ i, hX.eigenvalues i ∈ S) :
    supportProjection X = Polynomial.aeval X
      (Lagrange.interpolate S id (fun t : ℝ => if t = 0 then 0 else 1)) := by
  unfold supportProjection
  have hX' : IsSelfAdjoint X := hX
  rw [← cfc_polynomial _ X hX']
  apply cfc_congr
  intro t ht
  rw [hX.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  have := Lagrange.eval_interpolate_at_node (s := S) (v := id)
    (fun t : ℝ => if t = 0 then 0 else 1) (Set.injOn_id _) (hS i)
  simpa using this.symm

open QAlgorithms.Papers.Independent.Dependency50.P41
  QAlgorithms.Papers.Independent.Information100.P06 in
lemma X7P41_cq_supp {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v) (blocks : K → Matrix A A ℂ)
    (hb : ∀ k, (blocks k).IsHermitian) :
    supportProjection (cqOperator v blocks) =
      ∑ k, Matrix.kronecker (supportProjection (blocks k)) (pureDensity (v k)) := by
  classical
  have hH := X7P41_cq_herm v blocks hb
  set S : Finset ℝ := insert 0 (Finset.univ.image hH.eigenvalues ∪
    Finset.univ.biUnion (fun k => Finset.univ.image (hb k).eigenvalues)) with hSdef
  have h0 : (0:ℝ) ∈ S := Finset.mem_insert_self _ _
  rw [X7P41_supp_eq_aeval _ hH S (fun i => by simp [S])]
  rw [X7P41_cq_aeval v hv blocks]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [X7P41_supp_eq_aeval _ (hb k) S (fun i => by
      simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
        Finset.mem_univ, true_and]
      exact Or.inr (Or.inr ⟨k, i, rfl⟩))]
  · have := Lagrange.eval_interpolate_at_node (s := S) (v := id)
      (fun t : ℝ => if t = 0 then 0 else 1) (Set.injOn_id _) h0
    simpa using this

lemma X7P41_tr_pd_mul {B : Type} [Fintype B] (x : EuclideanSpace ℂ B) (σ : Matrix B B ℂ) :
    (pureDensity x * σ).trace = star (x : B → ℂ) ⬝ᵥ σ *ᵥ (x : B → ℂ) := by
  simp only [trace, diag, mul_apply, pureDensity, of_apply, dotProduct, mulVec, Pi.star_apply,
    RCLike.star_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma X7P41_w_nonneg {B : Type} [Fintype B] (x : EuclideanSpace ℂ B) (σ : Matrix B B ℂ)
    (hσ : σ.PosSemidef) : 0 ≤ (pureDensity x * σ).trace := by
  rw [X7P41_tr_pd_mul]; exact hσ.dotProduct_mulVec_nonneg _

lemma X7P41_sum_w_le {B : Type} {K : Type*} [Fintype B] [DecidableEq B] [Fintype K]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v) (σ : Matrix B B ℂ)
    (hσ : σ.PosSemidef) : ∑ k, ((pureDensity (v k) * σ).trace).re ≤ (σ.trace).re := by
  classical
  set P : Matrix B B ℂ := ∑ k, pureDensity (v k) with hP
  have hPP : P * P = P := by
    simp only [P, Finset.sum_mul, Finset.mul_sum, X7P41_pd_orth v hv, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hPH : Pᴴ = P := by
    simp only [P, conjTranspose_sum, (X7P41_pd_herm _).eq]
  set Q : Matrix B B ℂ := 1 - P
  have hQQ : Q * Q = Q := by
    simp only [Q, sub_mul, mul_sub, one_mul, mul_one, hPP]; abel
  have hQH : Qᴴ = Q := by simp [Q, conjTranspose_sub, hPH]
  have hQ : 0 ≤ (Q * σ).trace := by
    have h1 : (Q * σ).trace = (Qᴴ * σ * Q).trace := by
      calc (Q * σ).trace = ((Q * Q) * σ).trace := by rw [hQQ]
        _ = _ := by rw [hQH, mul_assoc, trace_mul_comm]
    rw [h1]; exact (hσ.conjTranspose_mul_mul_same Q).trace_nonneg
  have hsum : ∑ k, (pureDensity (v k) * σ).trace = σ.trace - (Q * σ).trace := by
    simp only [Q, sub_mul, one_mul, trace_sub, P, Finset.sum_mul, trace_sum]; ring
  have := (Complex.nonneg_iff.mp hQ).1
  rw [← Complex.re_sum, hsum, Complex.sub_re]
  have h1 : σ.trace.re - (Q * σ).trace.re ≤ σ.trace.re := by linarith
  exact h1

open QAlgorithms.Papers.Independent.Dependency50.P41
  QAlgorithms.Papers.Independent.Information100.P06 in
lemma X7P41_trace_formula {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v) (blocks : K → Matrix A A ℂ)
    (hb : ∀ k, (blocks k).IsHermitian) (σ : Matrix B B ℂ) :
    (supportProjection (cqOperator v blocks) * Matrix.kronecker (1 : Matrix A A ℂ) σ).trace =
      ∑ k, ((blocks k).rank : ℂ) * (pureDensity (v k) * σ).trace := by
  rw [X7P41_cq_supp v hv blocks hb, Finset.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.kronecker, ← mul_kronecker_mul, trace_kronecker, mul_one,
    X7P41_trace_supp _ (hb k)]

lemma X7P41_logExt_mono {x y : ℝ} (h : x ≤ y) :
    QAlgorithms.Papers.Independent.Dependency50.P41.logExtended x ≤
      QAlgorithms.Papers.Independent.Dependency50.P41.logExtended y := by
  unfold QAlgorithms.Papers.Independent.Dependency50.P41.logExtended
  split_ifs with h1 h2
  · exact le_rfl
  · exact bot_le
  · linarith
  · exact EReal.coe_le_coe_iff.mpr (Real.logb_le_logb_of_le (by norm_num) (by linarith) h)

lemma X7P41_pd_density {B : Type} [Fintype B] [DecidableEq B] (x : EuclideanSpace ℂ B)
    (hx : ‖x‖ = 1) : IsDensityMatrix (pureDensity x) := by
  have hv : pureDensity x = vecMulVec (x : B → ℂ) (star (x : B → ℂ)) := by
    ext a b; simp [pureDensity, vecMulVec]
  refine ⟨hv ▸ posSemidef_vecMulVec_self_star _, ?_⟩
  have h1 : inner ℂ x x = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hx]; simp
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
  rw [← h1]
  simp [trace, pureDensity, dotProduct]

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P41 in
theorem solution {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (v : K → EuclideanSpace ℂ B) (hv : Orthonormal ℂ v)
    (blocks : K → Op A) (hblocks : ∀ k, (blocks k).PosSemidef) :
    conditionalH0 (cqOperator v blocks) = ⨆ k, logRank (blocks k) := by
  have hb : ∀ k, (blocks k).IsHermitian := fun k => (hblocks k).isHermitian
  set R : ℕ := Finset.univ.sup (fun k => (blocks k).rank) with hR
  have hle : ∀ k, (blocks k).rank ≤ R := fun k =>
    Finset.le_sup (f := fun k => (blocks k).rank) (Finset.mem_univ k)
  have hatt : Nonempty K → ∃ k, (blocks k).rank = R := by
    intro hK
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun k => (blocks k).rank)
    exact ⟨k, hk.symm⟩
  have hR0 : IsEmpty K → R = 0 := by
    intro hK; simp [hR, Finset.univ_eq_empty]
  have hrhs : (⨆ k, logRank (blocks k)) = logExtended (R : ℝ) := by
    apply le_antisymm
    · exact iSup_le fun k => X7P41_logExt_mono (by exact_mod_cast hle k)
    · rcases isEmpty_or_nonempty K with hK | hK
      · rw [hR0 hK]; simp [logExtended]
      · obtain ⟨k, hk⟩ := hatt hK
        exact le_iSup_of_le k (by rw [logRank, hk])
  rw [hrhs]
  unfold conditionalH0
  apply le_antisymm
  · apply sSup_le
    rintro h ⟨σ, hσ, rfl⟩
    apply X7P41_logExt_mono
    rw [X7P41_trace_formula v hv blocks hb σ, Complex.re_sum]
    have hw : ∀ k, 0 ≤ ((pureDensity (v k) * σ).trace).re := fun k =>
      (Complex.nonneg_iff.mp (X7P41_w_nonneg (v k) σ hσ.1)).1
    have hs := X7P41_sum_w_le v hv σ hσ.1
    rw [hσ.2, Complex.one_re] at hs
    calc ∑ k, (((blocks k).rank : ℂ) * (pureDensity (v k) * σ).trace).re
        = ∑ k, ((blocks k).rank : ℝ) * ((pureDensity (v k) * σ).trace).re := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp
      _ ≤ ∑ k, (R : ℝ) * ((pureDensity (v k) * σ).trace).re := by
          refine Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle k) (hw k)
      _ = (R : ℝ) * ∑ k, ((pureDensity (v k) * σ).trace).re := by rw [Finset.mul_sum]
      _ ≤ (R : ℝ) * 1 := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
      _ = R := mul_one _
  · rcases isEmpty_or_nonempty K with hK | hK
    · rw [hR0 hK]; simp [logExtended]
    · obtain ⟨k0, hk0⟩ := hatt hK
      apply le_sSup
      refine ⟨pureDensity (v k0), X7P41_pd_density _ (hv.1 k0), ?_⟩
      rw [X7P41_trace_formula v hv blocks hb]
      congr 1
      have : ∀ k, (pureDensity (v k) * pureDensity (v k0)).trace = if k = k0 then 1 else 0 := by
        intro k
        rw [X7P41_pd_orth v hv]
        split_ifs with h
        · subst h; exact (X7P41_pd_density _ (hv.1 k)).2
        · simp
      simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hk0]; simp

end
