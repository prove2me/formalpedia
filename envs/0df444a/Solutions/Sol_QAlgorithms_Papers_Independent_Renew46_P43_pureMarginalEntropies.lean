-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.pureMarginalEntropies
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:31:07.911642+00:00
-- url     : https://prove2.me/submissions/d69e6539-d756-4db6-9738-ce6b63eb3d5f

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

/-- Theorem A.12, PDF p.71: purity only on XY. The pullback by the surjective
multiplication map preserves that purity; ambient purity is not assumed. -/
theorem solution {X Y A : IntrinsicSystem} (E : Embedding X A) (F : Embedding Y A)
    (hcompat : CommutingImages E.map F.map) (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hrho : A.IsState rho) (hpure : IsPure (jointState X Y E.map F.map rho)) :
    viewedEntropy X E.map rho = viewedEntropy Y F.map rho := by
  obtain ⟨v, -, hv⟩ := hpure
  let M : Matrix (Fin X.dim) (Fin Y.dim) ℂ := fun a b => v (a, b)
  have hJ : ∀ i k j l, jointState X Y E.map F.map rho (i, k) (j, l) = v (i, k) * conj (v (j, l)) := by
    intro i k j l
    rw [hv]; rfl
  have hX : intrinsicRestriction X E.map rho = M * Mᴴ := by
    ext i j
    have e1 : (M * Mᴴ) i j = ∑ k, jointState X Y E.map F.map rho (i, k) (j, k) := by
      rw [Matrix.mul_apply]; simp only [hJ]; rfl
    rw [e1]
    unfold jointState intrinsicRestriction
    simp only [and_true]
    split_ifs with h
    · simp_rw [← Matrix.trace_sum, ← Matrix.mul_sum, ← map_sum, g79a_sum_single, F.unit, mul_one]
    · simp
  have hY : intrinsicRestriction Y F.map rho = Mᵀ * (Mᵀ)ᴴ := by
    ext k l
    have e1 : (Mᵀ * (Mᵀ)ᴴ) k l = ∑ i, jointState X Y E.map F.map rho (i, k) (i, l) := by
      rw [Matrix.mul_apply]; simp only [hJ]; rfl
    rw [e1]
    unfold jointState intrinsicRestriction
    simp only [true_and]
    split_ifs with h
    · simp_rw [← Matrix.trace_sum, ← Matrix.mul_sum, ← Finset.sum_mul, ← map_sum, g79a_sum_single,
        E.unit, one_mul]
    · simp
  unfold viewedEntropy
  rw [hX, hY, g79a_entropy_swap]


end

