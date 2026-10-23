-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P11.exampleBell
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:35:29.978808+00:00
-- url     : https://prove2.me/submissions/9e94671a-e552-4a76-8562-8d5232dd1cb6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P11
open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)
attribute [local instance] Classical.propDecidable Classical.decEq
lemma g79f_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
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

lemma g79f_pow_succ_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) : (M * Mᴴ) ^ (k + 1) = M * (Mᴴ * M) ^ k * Mᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma g79f_trace_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) :
    ((M * Mᴴ) ^ (k + 1)).trace = ((Mᵀ * (Mᵀ)ᴴ) ^ (k + 1)).trace := by
  have h1 : Mᵀ * (Mᵀ)ᴴ = (Mᴴ * M)ᵀ := by
    rw [Matrix.transpose_mul]; rfl
  rw [h1, ← Matrix.transpose_pow, Matrix.trace_transpose, g79f_pow_succ_mul, Matrix.mul_assoc,
    Matrix.trace_mul_comm, pow_succ, Matrix.mul_assoc]

lemma g79f_entropy_swap {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) : vnEntropy (M * Mᴴ) = vnEntropy (Mᵀ * (Mᵀ)ᴴ) := by
  unfold vnEntropy
  rw [g79f_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.isHermitian_mul_conjTranspose_self Mᵀ) _ (by simp) (g79f_trace_pow M)]

lemma g79f_vn_one_unit : vnEntropy (1 : Matrix Unit Unit ℂ) = 0 := by
  unfold vnEntropy
  rw [show (1 : Matrix Unit Unit ℂ) = algebraMap ℝ _ 1 from (map_one _).symm, cfc_algebraMap]
  simp

lemma g79f_vn_pure {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι)
    (h : IsState ψ) : vnEntropy (pureDensity ψ) = 0 := by
  let M : Matrix ι Unit ℂ := Matrix.of fun i _ => ψ i
  have h1 : pureDensity ψ = M * Mᴴ := by
    ext x y; simp [pureDensity, M, Matrix.mul_apply]
  have hn : ∑ i, ψ i * conj (ψ i) = 1 := by
    have h2 : ‖ψ‖ ^ 2 = 1 := by rw [h]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    have : (∑ i, ψ i * conj (ψ i)) = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [this, h2]; simp
  have h2 : Mᵀ * (Mᵀ)ᴴ = 1 := by
    ext x y
    simp [M, Matrix.mul_apply, hn]
  rw [h1, g79f_entropy_swap, h2, g79f_vn_one_unit]

lemma g79f_vn_half : vnEntropy (algebraMap ℝ (Matrix Bool Bool ℂ) (1/2)) = 1 := by
  unfold vnEntropy
  rw [cfc_algebraMap (R := ℝ) (A := Matrix Bool Bool ℂ) (1/2 : ℝ) (fun x : ℝ => x * Real.logb 2 x)]
  have hf : (1/2 : ℝ) * Real.logb 2 (1/2) = -1/2 := by
    rw [one_div, Real.logb_inv, Real.logb_self_eq_one one_lt_two]; ring
  rw [hf]
  simp [Matrix.trace, Matrix.algebraMap_matrix_apply]
  norm_num

lemma g79f_bell_state : IsState (QAlgorithms.Papers.Independent.Information100.P22.bell Bool) := by
  unfold IsState
  rw [EuclideanSpace.norm_eq]
  simp [QAlgorithms.Papers.Independent.Information100.P22.bell, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

lemma g79f_bell_marg : traceLeft (pureDensity (QAlgorithms.Papers.Independent.Information100.P22.bell Bool))
    = algebraMap ℝ (Matrix Bool Bool ℂ) (1/2) := by
  ext x y
  simp [traceLeft, pureDensity, QAlgorithms.Papers.Independent.Information100.P22.bell, Fintype.sum_bool, Matrix.algebraMap_matrix_apply]
  have : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 2⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; rfl
  split_ifs <;> simp [Complex.conj_ofReal, this]

lemma g79f_s_conj : conj (((Real.sqrt 2 : ℂ))⁻¹) = ((Real.sqrt 2 : ℂ))⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

lemma g79f_s_sq : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; rfl

theorem solution :
    IsState (QAlgorithms.Papers.Independent.Information100.P22.bell Bool) ∧ conditionalEntropy (pureDensity (QAlgorithms.Papers.Independent.Information100.P22.bell Bool)) = -1 ∧
    IsChannel bobPreparesBell ∧
    bellMergingOperation (pureDensity (QAlgorithms.Papers.Independent.Information100.P22.bell Bool)) = bellMergingTarget := by
  refine ⟨g79f_bell_state, ?_, ?_, ?_⟩
  · unfold conditionalEntropy
    rw [g79f_vn_pure _ g79f_bell_state, g79f_bell_marg, g79f_vn_half]; norm_num
  · set ψ := QAlgorithms.Papers.Independent.Information100.P22.bell Bool with hψ
    let E : Fin 1 → Matrix ((Bool × Bool) × Bool) Bool ℂ :=
      fun _ => Matrix.of fun p c => ψ p.1 * (if p.2 = c then 1 else 0)
    refine ⟨1, E, ?_, ?_⟩
    · unfold IsKrausFamily
      ext x y
      cases x <;> cases y <;>
      simp [Fin.sum_univ_one, Matrix.mul_apply, Matrix.conjTranspose_apply, E, Matrix.of_apply,
        Fintype.sum_prod_type, Matrix.one_apply, Fintype.sum_bool, hψ,
        QAlgorithms.Papers.Independent.Information100.P22.bell, g79f_s_conj, g79f_s_sq]
    · intro X
      ext p q
      obtain ⟨⟨a, b⟩, c⟩ := p
      obtain ⟨⟨a', b'⟩, c'⟩ := q
      simp only [krausApply, Fin.sum_univ_one, Matrix.mul_apply, Matrix.conjTranspose_apply, E,
        Matrix.of_apply, bobPreparesBell, pureDensity, Fintype.sum_bool, RCLike.star_def]
      cases c <;> cases c' <;> simp <;> ring
  · ext p q
    obtain ⟨a, ⟨b, c⟩, d⟩ := p
    obtain ⟨a', ⟨b', c'⟩, d'⟩ := q
    simp only [bellMergingOperation, productApply, bobPreparesBell, bellMergingTarget,
      Matrix.single_apply, Fintype.sum_bool]
    cases a <;> cases a' <;> cases d <;> cases d' <;> simp
