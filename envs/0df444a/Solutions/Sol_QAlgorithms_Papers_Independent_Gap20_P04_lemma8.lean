-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P04.lemma8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:31:18.747392+00:00
-- url     : https://prove2.me/submissions/29643f42-0e3e-46b7-a4bc-49f6cae98b29

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P04
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P04

open QAlgorithms

open QAlgorithms.Papers.Independent.Claimed50.P24
  (Dilation PhysicalDilation ChannelEB Hadamard EqualMax AdditiveMax
   dephasingDilation dephasingGamma cloningDilation)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel dilationPower)

open QAlgorithms.Papers.Independent.Information100.P32 (diagonal)

open QAlgorithms.Papers.Independent.Dependency50.P24 (ensembleHolevoBits)

open QAlgorithms.Papers.Independent.Gap48.P44 (cqTimeSharing ceTimeSharing)

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}

variable [Fintype I] [Fintype B] [Fintype E]

variable [Fintype J] [Fintype D] [Fintype F]

variable [DecidableEq I] [DecidableEq B] [DecidableEq E]

variable [DecidableEq J] [DecidableEq D] [DecidableEq F]

variable [Nonempty I] [Nonempty B] [Nonempty E]

variable [Nonempty J] [Nonempty D] [Nonempty F]

open scoped ComplexOrder

lemma g79d_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g79d_vn_nonneg {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ)
    (h : ρ.PosSemidef) (ht : ρ.trace = 1) : 0 ≤ vnEntropy ρ := by
  have hH := h.isHermitian
  unfold vnEntropy
  rw [g79d_cfc_trace hH]
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [ht] at this
    have h2 := congrArg Complex.re this
    simp at h2
    exact h2.symm
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => h.eigenvalues_nonneg i
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro i _
  exact mul_nonpos_of_nonneg_of_nonpos (hnn i) (Real.logb_nonpos (by norm_num) (hnn i) (hle i))

lemma g79d_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
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

lemma g79d_pow_succ_mul {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) : (M * Mᴴ) ^ (k + 1) = M * (Mᴴ * M) ^ k * Mᴴ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

lemma g79d_trace_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (k : ℕ) :
    ((M * Mᴴ) ^ (k + 1)).trace = ((Mᵀ * (Mᵀ)ᴴ) ^ (k + 1)).trace := by
  have h1 : Mᵀ * (Mᵀ)ᴴ = (Mᴴ * M)ᵀ := by
    rw [Matrix.transpose_mul]; rfl
  rw [h1, ← Matrix.transpose_pow, Matrix.trace_transpose, g79d_pow_succ_mul, Matrix.mul_assoc,
    Matrix.trace_mul_comm, pow_succ, Matrix.mul_assoc]

lemma g79d_entropy_swap {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) : vnEntropy (M * Mᴴ) = vnEntropy (Mᵀ * (Mᵀ)ᴴ) := by
  unfold vnEntropy
  rw [g79d_trace_cfc_eq _ _ (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.isHermitian_mul_conjTranspose_self Mᵀ) _ (by simp) (g79d_trace_pow M)]

lemma g79d_tl_eq {R X : Type} [Fintype R] [Fintype X] (psi : EuclideanSpace ℂ (R × X)) :
    traceLeft (pureDensity psi) =
      (Matrix.of fun (r : R) (i : X) => psi (r, i))ᵀ * ((Matrix.of fun (r : R) (i : X) => psi (r, i))ᵀ)ᴴ := by
  ext i j; simp [traceLeft, pureDensity, Matrix.mul_apply]

lemma g79d_norm_sum {X : Type} [Fintype X] (v : EuclideanSpace ℂ X) :
    ∑ i, v i * conj (v i) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma g79d_tl_density {R X : Type} [Fintype R] [Fintype X] [DecidableEq X]
    (psi : EuclideanSpace ℂ (R × X)) (h : ‖psi‖ = 1) :
    IsDensityMatrix (traceLeft (pureDensity psi)) := by
  refine ⟨?_, ?_⟩
  · rw [g79d_tl_eq]; exact Matrix.posSemidef_self_mul_conjTranspose _
  · have := g79d_norm_sum psi
    rw [h] at this
    simp only [one_pow, Complex.ofReal_one] at this
    rw [← this, Fintype.sum_prod_type, Finset.sum_comm]
    simp [Matrix.trace, traceLeft, pureDensity]

lemma g79d_rc_swap {I B E : Type} [Fintype I] [Fintype B] [Fintype E] [DecidableEq B] [DecidableEq E]
    (U : Matrix (B × E) I ℂ) (v : I → ℂ) :
    vnEntropy (receiverChannel U (Matrix.of fun i j => v i * conj (v j))) =
      vnEntropy (complementaryChannel U (Matrix.of fun i j => v i * conj (v j))) := by
  set M : Matrix B E ℂ := Matrix.of fun b e => ∑ i, U (b, e) i * v i with hM
  have h1 : receiverChannel U (Matrix.of fun i j => v i * conj (v j)) = M * Mᴴ := by
    ext b b'
    simp only [receiverChannel, traceRight, hM, Matrix.mul_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
    simp only [Complex.star_def]; ring
  have h2 : complementaryChannel U (Matrix.of fun i j => v i * conj (v j)) = Mᵀ * (Mᵀ)ᴴ := by
    ext e e'
    simp only [complementaryChannel, traceLeft, hM, Matrix.mul_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, star_sum, star_mul', Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
    simp only [Complex.star_def]; ring
  rw [h1, h2]; exact g79d_entropy_swap M

lemma g79d_vn_pure_zero {I : Type} [Fintype I] [DecidableEq I] (v : I → ℂ)
    (hv : ∑ i, v i * conj (v i) = 1) :
    vnEntropy (Matrix.of fun i j => v i * conj (v j)) = 0 := by
  set M : Matrix I (Fin 1) ℂ := Matrix.of fun i _ => v i with hM
  have h1 : (Matrix.of fun i j => v i * conj (v j)) = M * Mᴴ := by
    ext i j; simp [hM, Matrix.mul_apply]
  have h2 : Mᵀ * (Mᵀ)ᴴ = 1 := by
    ext a b
    fin_cases a; fin_cases b
    simp [hM, Matrix.mul_apply, hv]
  rw [h1, g79d_entropy_swap, h2]
  simp [vnEntropy]


/-- PDF p.19, Lemma 8: general one-use CE upper boundary, including lam=0.
At zero weight the proof's strict energy comparison fails; upper C(E) is the
figure-compatible boundary convention, not minimum-E selection among tied optimizers. -/
theorem solution (U : Dilation I B E) (hU : PhysicalDilation U)
    (lam : ℝ) (h0 : 0 ≤ lam) (e : PurifiedInputFamily I) (he : e.Valid)
    (hmax : IsGreatest (purifiedValues (ceScore U lam)) (ceScore U lam e)) :
    CEUpper (oneCE U) (jointInfo U e, inputEntropy e) := by
  have key : ∀ e' : PurifiedInputFamily I, e'.Valid → ceScore U lam e' ≤ ceScore U lam e :=
    fun e' he' => hmax.2 ⟨e', he', rfl⟩
  have hIE : 0 ≤ inputEntropy e := by
    unfold inputEntropy
    refine Finset.sum_nonneg (fun x _ => mul_nonneg (he.2.2.1 x) ?_)
    have hd := g79d_tl_density (e.psi x) (he.2.2.2.2 x)
    exact g79d_vn_nonneg _ hd.1 hd.2
  obtain ⟨i0⟩ := (inferInstance : Nonempty I)
  let e0 : PurifiedInputFamily I :=
    { labels := 1, reference := 1, prob := fun _ => 1,
      psi := fun _ => EuclideanSpace.single ((0 : Fin 1), i0) 1 }
  have he0 : e0.Valid := by
    refine ⟨by norm_num, by norm_num, fun _ => by norm_num, by simp [e0], fun _ => by simp [e0]⟩
  set v : I → ℂ := fun i => if i = i0 then 1 else 0 with hv
  have hin : ∀ x, e0.input x = Matrix.of fun i j => v i * conj (v j) := by
    intro x
    ext i j
    simp [e0, PurifiedInputFamily.input, traceLeft, pureDensity, hv]
  have hvs : ∑ i, v i * conj (v i) = 1 := by simp [hv]
  have hs0 : ceScore U lam e0 = 0 := by
    have havg : e0.average = Matrix.of fun i j => v i * conj (v j) := by
      simp [PurifiedInputFamily.average, hin, e0]
    simp only [ceScore, jointInfo, inputEntropy, ensembleReceiverEntropy,
      conditionalEnvironmentEntropy, havg, hin]
    simp [e0, g79d_vn_pure_zero v hvs, g79d_rc_swap U v]
  have hJ : 0 ≤ jointInfo U e := by
    have := key e0 he0
    rw [hs0] at this
    unfold ceScore at this
    nlinarith [mul_nonneg h0 hIE]
  refine ⟨⟨hJ, hIE, e, he, le_rfl, le_rfl⟩, ?_⟩
  rintro s ⟨hs1, hs2, e', he', hj, hi⟩ hle
  have := key e' he'
  unfold ceScore at this
  simp only at hle ⊢
  have : lam * inputEntropy e' ≤ lam * inputEntropy e :=
    mul_le_mul_of_nonneg_left (hi.trans hle) h0
  linarith



end
