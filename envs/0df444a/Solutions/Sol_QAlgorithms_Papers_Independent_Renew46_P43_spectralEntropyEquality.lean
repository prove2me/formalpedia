-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.spectralEntropyEquality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:11:18.260178+00:00
-- url     : https://prove2.me/submissions/256eb323-ee9f-4fed-9ae3-192f07735c41

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

lemma g79a_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

lemma g79a_pow_succ_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) : (M * Mᴴ) ^ (k + 1) = M * (Mᴴ * M) ^ k * Mᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma g79a_trace_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) :
    ((M * Mᴴ) ^ (k + 1)).trace = ((Mᵀ * (Mᵀ)ᴴ) ^ (k + 1)).trace := by
  have h1 : Mᵀ * (Mᵀ)ᴴ = (Mᴴ * M)ᵀ := by
    rw [Matrix.transpose_mul]; rfl
  rw [h1, ← Matrix.transpose_pow, Matrix.trace_transpose, g79a_pow_succ_mul, Matrix.mul_assoc,
    Matrix.trace_mul_comm, pow_succ, Matrix.mul_assoc]

lemma g79a_entropy_swap {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) : vnEntropy (M * Mᴴ) = vnEntropy (Mᵀ * (Mᵀ)ᴴ) := by
  unfold vnEntropy
  rw [g79a_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.isHermitian_mul_conjTranspose_self Mᵀ) _ (by simp) (g79a_trace_pow M)]

lemma g79a_sum_single {n : ℕ} : ∑ k : Fin n, (Matrix.single k k (1:ℂ)) = 1 := by
  ext a b
  rw [Matrix.sum_apply, Finset.sum_eq_single a]
  · by_cases h : a = b <;> simp [h, Matrix.single_apply, Matrix.one_apply]
  · intro k _ hk; simp [Matrix.single_apply]; intro h; exact absurd h hk
  · simp

lemma g79a_single_inBlocks {d : ℕ} (blk : Fin d → ℕ) (i j : Fin d) (h : blk i = blk j) :
    InBlocks blk (Matrix.single i j (1 : ℂ)) := by
  intro a b hab
  rw [Matrix.single_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl⟩ := h1; exact absurd h hab
  · rfl


section G79D
open Polynomial
lemma g79a_cfc_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  set A := Matrix.diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hA, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ i, p.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f) (i := d i)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    exact this
  have hspec : ∀ x ∈ spectrum ℝ A, ∃ i, d i = x := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, hA, spectrum_diagonal,
      Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  have h1 : cfc f A = cfc p.eval A := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := hspec x hx
    exact (hp i).symm
  rw [h1, cfc_polynomial p A]
  rw [hA, show Matrix.diagonal (fun i => (d i : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl, Polynomial.aeval_algHom_apply]
  rw [show Matrix.diagonal (fun i => (f (d i) : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (f (d i) : ℂ)) from rfl]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval, hp]
  rfl
end G79D

lemma g79a_inBlocks_mul {d : ℕ} {blk : Fin d → ℕ} {T U : Matrix (Fin d) (Fin d) ℂ}
    (hT : InBlocks blk T) (hU : InBlocks blk U) : InBlocks blk (T * U) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  by_cases h : blk a = blk k
  · rw [hU k b (by rw [← h]; exact hab), mul_zero]
  · rw [hT a k h, zero_mul]

lemma g79a_inBlocks_add {d : ℕ} {blk : Fin d → ℕ} {T U : Matrix (Fin d) (Fin d) ℂ}
    (hT : InBlocks blk T) (hU : InBlocks blk U) : InBlocks blk (T + U) := by
  intro a b hab; simp [hT a b hab, hU a b hab]

lemma g79a_inBlocks_smul {d : ℕ} {blk : Fin d → ℕ} {T : Matrix (Fin d) (Fin d) ℂ} (c : ℂ)
    (hT : InBlocks blk T) : InBlocks blk (c • T) := by
  intro a b hab; simp [hT a b hab]

lemma g79a_inBlocks_sum {d : ℕ} {blk : Fin d → ℕ} {ι : Type*} (s : Finset ι)
    (T : ι → Matrix (Fin d) (Fin d) ℂ) (hT : ∀ i, InBlocks blk (T i)) :
    InBlocks blk (∑ i ∈ s, T i) := by
  intro a b hab; rw [Matrix.sum_apply]; exact Finset.sum_eq_zero (fun i _ => hT i a b hab)

lemma g79a_inBlocks_one {d : ℕ} (blk : Fin d → ℕ) : InBlocks blk (1 : Matrix (Fin d) (Fin d) ℂ) := by
  intro a b hab; rw [Matrix.one_apply_ne]; intro h; exact hab (by rw [h])

lemma g79a_inBlocks_pow {d : ℕ} {blk : Fin d → ℕ} {T : Matrix (Fin d) (Fin d) ℂ}
    (hT : InBlocks blk T) (n : ℕ) : InBlocks blk (T ^ n) := by
  induction n with
  | zero => simpa using g79a_inBlocks_one blk
  | succ n ih => rw [pow_succ]; exact g79a_inBlocks_mul ih hT

lemma g79a_emb_pow {X A : IntrinsicSystem} (E : Embedding X A) {T : Matrix (Fin X.dim) (Fin X.dim) ℂ}
    (hT : InBlocks X.block T) (n : ℕ) : E.map (T ^ n) = (E.map T) ^ n := by
  induction n with
  | zero => simp [E.unit]
  | succ n ih => rw [pow_succ, E.mul _ _ (g79a_inBlocks_pow hT n) hT, ih, pow_succ]

/-- properties of a pure state v v* -/
lemma g79a_pure {I : Type} [Fintype I] [DecidableEq I] {P : Matrix I I ℂ} (hP : IsPure P) :
    P * P = P ∧ P.trace = 1 ∧ Pᴴ = P ∧ ∃ v : I → ℂ, ∀ M : Matrix I I ℂ,
      P * M * P = (∑ a, ∑ b, star (v a) * M a b * v b) • P := by
  obtain ⟨v, hv, rfl⟩ := hP
  have hn : ∑ k, star (v k) * v k = 1 := by
    have h := EuclideanSpace.norm_eq v
    rw [hv] at h
    have h2 : ∑ k, ‖v k‖ ^ 2 = 1 := by
      have := congrArg (· ^ 2) h
      simp only [one_pow] at this
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))] at this
      exact this.symm
    have : ∑ k, star (v k) * v k = ((∑ k, ‖v k‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [RCLike.star_def, mul_comm, RCLike.mul_conj]; norm_cast
    rw [this, h2]; simp
  refine ⟨?_, ?_, ?_, ⟨v, fun M => ?_⟩⟩
  · ext a b
    simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply]
    have : ∑ k, v a * (starRingEnd ℂ) (v k) * (v k * (starRingEnd ℂ) (v b)) =
        v a * (starRingEnd ℂ) (v b) * ∑ k, star (v k) * v k := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [RCLike.star_def]; ring
    rw [this, hn, mul_one]
  · simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply]
    rw [← hn]; refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [RCLike.star_def]; ring
  · ext a b; simp [pureDensity, mul_comm]
  · ext x y
    simp only [pureDensity, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    simp only [RCLike.star_def]; ring

lemma g79a_spec_clause1 {A : IntrinsicSystem} {m : ℕ}
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : A.IsState rho)
    (p : Fin m → ℝ) (P : Fin m → Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hP : ∀ i, A.IsPureState (P i))
    (hcomplete : ∑ i, P i = 1) (hdecomp : rho = ∑ i, (p i : ℂ) • P i)
    (X : IntrinsicSystem) (E : Embedding X A)
    (hT : ∀ i, ∃ T, InBlocks X.block T ∧ E.map T = P i) :
    viewedEntropy X E.map rho = vnEntropy rho := by
  choose T hTb hTE using hT
  have hPp := fun i => g79a_pure (hP i).1
  choose c hc using fun i => (hPp i).2.2.2
  have hfaith := E.faithful
  -- T_i is an idempotent
  have hTT : ∀ i, T i * T i = T i := fun i => hfaith _ _ (g79a_inBlocks_mul (hTb i) (hTb i)) (hTb i)
    (by rw [E.mul _ _ (hTb i) (hTb i), hTE, (hPp i).1])
  -- T_i Y T_i = c T_i
  have hTYT : ∀ i (Y : Matrix (Fin X.dim) (Fin X.dim) ℂ), InBlocks X.block Y →
      T i * Y * T i = (∑ a, ∑ b, star (c i a) * E.map Y a b * c i b) • T i := by
    intro i Y hY
    apply hfaith _ _ (g79a_inBlocks_mul (g79a_inBlocks_mul (hTb i) hY) (hTb i))
      (g79a_inBlocks_smul _ (hTb i))
    rw [E.mul _ _ (g79a_inBlocks_mul (hTb i) hY) (hTb i), E.mul _ _ (hTb i) hY, hTE, map_smul, hTE,
      hc i]
  -- sum T_i = 1
  have hTsum : ∑ i, T i = 1 := hfaith _ _ (g79a_inBlocks_sum _ _ hTb) (g79a_inBlocks_one _)
    (by rw [map_sum, E.unit]; simp_rw [hTE]; exact hcomplete)
  -- T_i hermitian
  have hTh : ∀ i, (T i)ᴴ = T i := by
    intro i
    have hb : InBlocks X.block (T i)ᴴ := by
      intro a b hab; simp [Matrix.conjTranspose_apply, hTb i b a (Ne.symm hab)]
    exact hfaith _ _ hb (hTb i) (by rw [E.star _ (hTb i), hTE, (hPp i).2.2.1])
  -- trace T_i = 1
  have hTtr : ∀ i, (T i).trace = 1 := by
    intro i
    have hne : T i ≠ 0 := by
      intro h0
      have := (hPp i).2.1
      rw [← hTE i, h0, map_zero, Matrix.trace_zero] at this
      exact zero_ne_one this
    have hdiag : ∀ a, T i a a = ∑ k, star (T i k a) * T i k a := by
      intro a
      conv_lhs => rw [← hTT i]
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have := congrFun (congrFun (hTh i) a) k
      rw [Matrix.conjTranspose_apply] at this
      rw [← this]
    obtain ⟨a, haa⟩ : ∃ a, T i a a ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hne
      ext x y
      have h1 := hdiag y
      rw [hcon y] at h1
      have h2 : ∀ k, star (T i k y) * T i k y = ((‖T i k y‖ ^ 2 : ℝ) : ℂ) := by
        intro k; rw [RCLike.star_def, mul_comm, RCLike.mul_conj]; norm_cast
      simp_rw [h2] at h1
      have h3 : ∑ k, ‖T i k y‖ ^ 2 = 0 := by exact_mod_cast h1.symm
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖T i k y‖)).mp h3 x
        (Finset.mem_univ _)
      simpa using this
    have hY := hTYT i (Matrix.single a a 1) (g79a_single_inBlocks _ a a rfl)
    set γ := ∑ a', ∑ b, star (c i a') * E.map (Matrix.single a a 1) a' b * c i b
    have hent : ∀ x y, T i x a * T i a y = γ * T i x y := by
      intro x y
      have := congrFun (congrFun hY x) y
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul] at this
      rw [← this]
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · simp
      · intro b _ hb
        rw [Finset.sum_eq_zero]; · simp
        intro k _; simp [Ne.symm hb]
      · simp
    have hγ : γ = T i a a := by
      have := hent a a
      have h' : T i a a * T i a a = T i a a * T i a a := rfl
      exact (mul_right_cancel₀ haa (this.symm.trans (by ring))).symm.trans rfl |>.symm
    have htr : ∑ x, T i x a * T i a x = T i a a := by
      conv_rhs => rw [← hTT i]
      rw [Matrix.mul_apply]; exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)
    have : T i a a = γ * (T i).trace := by
      rw [← htr, Matrix.trace, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => hent x x)
    rw [hγ] at this
    have := mul_left_cancel₀ haa (this.symm.trans (mul_one _).symm)
    exact this
  -- trace functional
  have hφ : ∀ Y, InBlocks X.block Y → (E.map Y).trace = Y.trace := by
    intro Y hY
    have e1 : (E.map Y).trace = ∑ i, (∑ a, ∑ b, star (c i a) * E.map Y a b * c i b) := by
      have : (E.map Y).trace = ∑ i, (P i * E.map Y * P i).trace := by
        conv_lhs => rw [← Matrix.mul_one (E.map Y), ← hcomplete, Matrix.mul_sum, Matrix.trace_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm (P i), Matrix.mul_assoc, (hPp i).1]
      rw [this]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hc i, Matrix.trace_smul, (hPp i).2.1, smul_eq_mul, mul_one]
    have e2 : Y.trace = ∑ i, (∑ a, ∑ b, star (c i a) * E.map Y a b * c i b) := by
      have : Y.trace = ∑ i, (T i * Y * T i).trace := by
        conv_lhs => rw [← Matrix.mul_one Y, ← hTsum, Matrix.mul_sum, Matrix.trace_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm (T i), Matrix.mul_assoc, hTT i]
      rw [this]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hTYT i Y hY, Matrix.trace_smul, hTtr i, smul_eq_mul, mul_one]
    rw [e1, e2]
  -- the restricted state equals S
  set S := ∑ i, (p i : ℂ) • T i with hS
  have hSb : InBlocks X.block S := g79a_inBlocks_sum _ _ (fun i => g79a_inBlocks_smul _ (hTb i))
  have hES : E.map S = rho := by
    rw [hS, map_sum, hdecomp]; simp_rw [map_smul, hTE]
  have hσ : intrinsicRestriction X E.map rho = S := by
    ext a b
    simp only [intrinsicRestriction]
    split_ifs with h
    · rw [← hES, ← E.mul _ _ hSb (g79a_single_inBlocks _ b a h.symm),
        hφ _ (g79a_inBlocks_mul hSb (g79a_single_inBlocks _ b a h.symm)), Matrix.trace_mul_comm,
        Matrix.trace_single_mul]
      simp
    · exact (hSb a b h).symm
  have hSh : S.IsHermitian := by
    rw [hS]; unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.conjTranspose_smul, hTh i]; simp
  unfold viewedEntropy vnEntropy
  rw [hσ, g79a_trace_cfc_eq S rho hSh hrho.1.1.isHermitian _ (by simp)]
  intro k
  rw [← hES, ← g79a_emb_pow E hSb, hφ _ (g79a_inBlocks_pow hSb _)]

lemma g79a_eta (t : ℝ) : -t * Real.logb 2 t = Real.negMulLog t / Real.log 2 := by
  simp [Real.negMulLog, Real.logb]; ring


lemma g79a_spec_clause2 {A : IntrinsicSystem} {m : ℕ}
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : A.IsState rho)
    (p : Fin m → ℝ) (P : Fin m → Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hP : ∀ i, A.IsPureState (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (hdecomp : rho = ∑ i, (p i : ℂ) • P i) :
    countableEntropy (fun i => effectProb rho (P i)) = ENNReal.ofReal (vnEntropy rho) := by
  have hPp := fun i => g79a_pure (hP i).1
  have hmulP : ∀ (q : Fin m → ℂ) i, (∑ j, q j • P j) * P i = q i • P i := by
    intro q i
    rw [Finset.sum_mul, Finset.sum_eq_single i]
    · rw [Matrix.smul_mul, (hPp i).1]
    · intro j _ hj; rw [Matrix.smul_mul, horth j i hj, smul_zero]
    · simp
  have hpow : ∀ n : ℕ, rho ^ (n + 1) = ∑ i, ((p i : ℂ) ^ (n + 1)) • P i := by
    intro n
    induction n with
    | zero => simp [hdecomp]
    | succ n ih =>
      rw [pow_succ, ih, hdecomp, Matrix.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.mul_smul, hmulP (fun j => (p j : ℂ) ^ (n + 1)) i, smul_smul]
      congr 1; ring
  have htrpow : ∀ n : ℕ, (rho ^ (n + 1)).trace = ∑ i, (p i : ℂ) ^ (n + 1) := by
    intro n
    rw [hpow, Matrix.trace_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.trace_smul, (hPp i).2.1, smul_eq_mul, mul_one]
  have hsum : ∑ i, p i = 1 := by
    have := htrpow 0
    rw [zero_add, pow_one, hrho.1.2] at this
    simp_rw [pow_one] at this
    have h2 := congrArg Complex.re this
    simp only [Complex.re_sum, Complex.ofReal_re, Complex.one_re] at h2
    linarith
  have hp1 : ∀ i, p i ≤ 1 := fun i => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  have heff : ∀ i, effectProb rho (P i) = p i := by
    intro i
    unfold effectProb
    rw [hdecomp, hmulP (fun j => (p j : ℂ)) i, Matrix.trace_smul, (hPp i).2.1]
    simp
  have hD : (Matrix.diagonal (fun i => (p i : ℂ))).IsHermitian := by
    unfold Matrix.IsHermitian; rw [Matrix.diagonal_conjTranspose]; congr 1; funext i; simp
  have hvn : vnEntropy rho = ∑ i, -p i * Real.logb 2 (p i) := by
    have : vnEntropy rho = vnEntropy (Matrix.diagonal (fun i => (p i : ℂ))) := by
      unfold vnEntropy
      rw [g79a_trace_cfc_eq rho _ hrho.1.1.isHermitian hD _ (by simp)]
      intro k
      rw [htrpow, Matrix.diagonal_pow, Matrix.trace_diagonal]
      rfl
    rw [this]
    unfold vnEntropy
    rw [g79a_cfc_diag, Matrix.trace_diagonal, Complex.re_sum, ← Finset.sum_neg_distrib]
    simp
  have hη : ∀ i, 0 ≤ -p i * Real.logb 2 (p i) := by
    intro i; rw [g79a_eta]
    exact div_nonneg (Real.negMulLog_nonneg (hp i) (hp1 i)) (Real.log_nonneg (by norm_num))
  unfold countableEntropy
  simp_rw [heff]
  rw [tsum_fintype, hvn, ENNReal.ofReal_sum_of_nonneg (fun i _ => hη i)]

/-- Equality cases following Theorem A.10, PDF p.71. Any subsystem containing
the full fine spectral resolution preserves entropy, as does its spectral observable. -/
theorem solution {A : IntrinsicSystem} {m : ℕ}
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : A.IsState rho)
    (p : Fin m → ℝ) (P : Fin m → Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hP : ∀ i, A.IsPureState (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (hcomplete : ∑ i, P i = 1)
    (hdecomp : rho = ∑ i, (p i : ℂ) • P i) :
    (∀ (X : IntrinsicSystem) (E : Embedding X A),
      (∀ i, ∃ T, InBlocks X.block T ∧ E.map T = P i) → viewedEntropy X E.map rho = vnEntropy rho) ∧
    countableEntropy (fun i => effectProb rho (P i)) = ENNReal.ofReal (vnEntropy rho) := by
  exact ⟨fun X E hT => g79a_spec_clause1 rho hrho p P hP hcomplete hdecomp X E hT,
    g79a_spec_clause2 rho hrho p P hp hP horth hdecomp⟩


end

