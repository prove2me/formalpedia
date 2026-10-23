-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P04.generalizedDephasingStructure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:07:13.903257+00:00
-- url     : https://prove2.me/submissions/7806253a-3c6a-4b87-8e14-5aac1b83fe0d

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

lemma g79d_pure_eq {X : Type} [Fintype X] (v : EuclideanSpace ℂ X) :
    pureDensity v = (Matrix.of fun (i : X) (_ : Fin 1) => v i) * (Matrix.of fun (i : X) (_ : Fin 1) => v i)ᴴ := by
  ext i j; simp [pureDensity, Matrix.mul_apply]

lemma g79d_pure_density {X : Type} [Fintype X] (v : EuclideanSpace ℂ X) (h : ‖v‖ = 1) :
    IsDensityMatrix (pureDensity v) := by
  refine ⟨?_, ?_⟩
  · rw [g79d_pure_eq]; exact Matrix.posSemidef_self_mul_conjTranspose _
  · have := g79d_norm_sum v
    rw [h] at this
    simp only [one_pow, Complex.ofReal_one] at this
    rw [← this]
    simp [Matrix.trace, pureDensity]

lemma g79d_eb_mp {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (Φ : Superop (Fin a) (Fin b))
    (P : Fin a → Matrix (Fin b) (Fin b) ℂ) (hP : ∀ k, IsDensityMatrix (P k))
    (hΦ : ∀ rho, Φ rho = ∑ k, rho k k • P k) :
    QAlgorithms.Papers.Independent.Dependency50.P41.EntanglementBreaking ha hb Φ := by
  intro psi hpsi
  let col : Fin a → EuclideanSpace ℂ (Fin a) := fun k => WithLp.toLp 2 (fun r => psi (r, k))
  let w : Fin a → ℝ := fun k => ‖col k‖ ^ 2
  let A : Fin a → Matrix (Fin a) (Fin a) ℂ := fun k =>
    if w k = 0 then pureDensity (EuclideanSpace.single (⟨0, ha⟩ : Fin a) (1 : ℂ))
    else ((w k)⁻¹ : ℂ) • pureDensity (col k)
  have hcolsum : ∀ k, ∑ r, psi (r, k) * conj (psi (r, k)) = ((w k : ℝ) : ℂ) := by
    intro k
    rw [show ((w k : ℝ) : ℂ) = ((‖col k‖ ^ 2 : ℝ) : ℂ) from rfl, ← g79d_norm_sum]
  refine ⟨a, w, A, P, fun k => by positivity, ?_, fun k => ⟨?_, hP k⟩, ?_⟩
  · have h1 := g79d_norm_sum psi
    rw [hpsi] at h1
    simp only [one_pow, Complex.ofReal_one] at h1
    have h2 : ((∑ k, w k : ℝ) : ℂ) = 1 := by
      rw [← h1, Complex.ofReal_sum, Fintype.sum_prod_type, Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => (hcolsum k).symm)
    exact_mod_cast h2
  · by_cases hw : w k = 0
    · simp only [A, hw, if_true]
      exact g79d_pure_density _ (by simp)
    · simp only [A, hw, if_false]
      have hd : (pureDensity (col k)).PosSemidef := by
        rw [g79d_pure_eq]; exact Matrix.posSemidef_self_mul_conjTranspose _
      refine ⟨?_, ?_⟩
      · apply Matrix.PosSemidef.smul hd
        have : (0:ℝ) ≤ (w k)⁻¹ := inv_nonneg.mpr (by positivity)
        exact_mod_cast (Complex.zero_le_real.mpr this)
      · have h3 : (pureDensity (col k)).trace = ((w k : ℝ) : ℂ) := by
          rw [Matrix.trace]
          simp only [pureDensity, Matrix.diag, Matrix.of_apply, col, PiLp.toLp_apply]
          exact hcolsum k
        rw [Matrix.trace_smul, h3, smul_eq_mul]
        have : ((w k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
        push_cast
        field_simp
  · ext p q
    simp only [idTensorSuperop, hΦ, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul, pureDensity]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hw : w k = 0
    · have h0 : ∀ r, psi (r, k) = 0 := by
        have : col k = 0 := by
          have : ‖col k‖ = 0 := by
            have := hw; simp only [w] at this; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
          exact norm_eq_zero.mp this
        intro r
        have := congrArg (fun v : EuclideanSpace ℂ (Fin a) => v r) this
        simpa [col] using this
      simp [h0, hw]
    · simp only [A, hw, if_false, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      have : ((w k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
      simp only [col, PiLp.toLp_apply, pureDensity, Matrix.of_apply]
      field_simp

lemma g79d_eb_prep {B E : Type} [Fintype B] [Fintype E] [DecidableEq B] [DecidableEq E]
    [Nonempty B] [Nonempty E] (Φ : Superop B E) (xi : B → EuclideanSpace ℂ E)
    (hxi : ∀ b, ‖xi b‖ = 1) (hΦ : ∀ rho, Φ rho = ∑ b, rho b b • pureDensity (xi b)) :
    QAlgorithms.Papers.Independent.Claimed50.P24.ChannelEB Φ := by
  unfold QAlgorithms.Papers.Independent.Claimed50.P24.ChannelEB
  apply g79d_eb_mp _ _ _
    (fun k => pureDensity (WithLp.toLp 2 (fun i => xi ((Fintype.equivFin B).symm k) ((Fintype.equivFin E).symm i))))
  · intro k
    apply g79d_pure_density
    have h1 := hxi ((Fintype.equivFin B).symm k)
    rw [EuclideanSpace.norm_eq] at h1 ⊢
    rw [← h1]
    congr 1
    simp only [PiLp.toLp_apply]
    exact Equiv.sum_comp (Fintype.equivFin E).symm (fun e => ‖xi ((Fintype.equivFin B).symm k) e‖ ^ 2)
  · intro rho
    ext i j
    refine (congrFun (congrFun (hΦ _) _) _).trans ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pureDensity, Matrix.of_apply,
      PiLp.toLp_apply]
    rw [← Equiv.sum_comp (Fintype.equivFin B).symm]
    simp

lemma g79d_conj_ite (p : Prop) [Decidable p] (a : ℂ) :
    (starRingEnd ℂ) (if p then a else 0) = if p then (starRingEnd ℂ) a else 0 := by
  split_ifs <;> simp

lemma g79d_gd_comp {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (v : I → EuclideanSpace ℂ E) (rho : Matrix I I ℂ) :
    complementaryChannel (QAlgorithms.Papers.Independent.Gap20.P04.gdDilation v) rho =
      ∑ i, rho i i • pureDensity (v i) := by
  ext e f
  simp only [complementaryChannel, traceLeft, QAlgorithms.Papers.Independent.Gap20.P04.gdDilation,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, pureDensity]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [g79d_conj_ite, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]
  try ring

lemma g79d_gd_recv {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (v : I → EuclideanSpace ℂ E) (rho : Matrix I I ℂ) :
    receiverChannel (QAlgorithms.Papers.Independent.Gap20.P04.gdDilation v) rho =
      Matrix.of fun b c => rho b c * ∑ e, v b e * conj (v c e) := by
  ext b c
  simp only [receiverChannel, traceRight, QAlgorithms.Papers.Independent.Gap20.P04.gdDilation,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [g79d_conj_ite, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]
  try ring

lemma g79d_unit_sum {E : Type} [Fintype E] (w : EuclideanSpace ℂ E) (h : ‖w‖ = 1) :
    ∑ e, w e * conj (w e) = 1 := by
  have := g79d_norm_sum w
  rw [h] at this
  simpa using this

lemma g79d_gd_recv_diag {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (v : I → EuclideanSpace ℂ E) (hv : ∀ i, ‖v i‖ = 1) (rho : Matrix I I ℂ) :
    receiverChannel (QAlgorithms.Papers.Independent.Gap20.P04.gdDilation v)
      (QAlgorithms.Papers.Independent.Information100.P32.diagonal rho) =
      QAlgorithms.Papers.Independent.Information100.P32.diagonal rho := by
  rw [g79d_gd_recv]
  ext b c
  simp only [QAlgorithms.Papers.Independent.Information100.P32.diagonal, Matrix.of_apply]
  split_ifs with h
  · subst h; rw [g79d_unit_sum _ (hv b), mul_one]
  · simp

lemma g79d_gd_diag_recv {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (v : I → EuclideanSpace ℂ E) (hv : ∀ i, ‖v i‖ = 1) (rho : Matrix I I ℂ) :
    QAlgorithms.Papers.Independent.Information100.P32.diagonal
      (receiverChannel (QAlgorithms.Papers.Independent.Gap20.P04.gdDilation v) rho) =
      QAlgorithms.Papers.Independent.Information100.P32.diagonal rho := by
  rw [g79d_gd_recv]
  ext b c
  simp only [QAlgorithms.Papers.Independent.Information100.P32.diagonal, Matrix.of_apply]
  split_ifs with h
  · subst h; rw [g79d_unit_sum _ (hv b), mul_one]
  · rfl

lemma g79d_gd_comp_diag {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (v : I → EuclideanSpace ℂ E) (rho : Matrix I I ℂ) :
    complementaryChannel (QAlgorithms.Papers.Independent.Gap20.P04.gdDilation v)
      (QAlgorithms.Papers.Independent.Information100.P32.diagonal rho) =
      complementaryChannel (QAlgorithms.Papers.Independent.Gap20.P04.gdDilation v) rho := by
  rw [g79d_gd_comp, g79d_gd_comp]
  simp [QAlgorithms.Papers.Independent.Information100.P32.diagonal]


/-- PDF pp.5--6, (10): generalized dephasing is Hadamard and commutes with complete
 dephasing; the complement depends only on input diagonals. No orthogonality of v_i required. -/
theorem solution (v : I → EuclideanSpace ℂ E)
    (hI : Nonempty I) (hv : ∀ i, ‖v i‖ = 1) :
    PhysicalDilation (gdDilation v) ∧ Hadamard (gdDilation v) ∧
    (∀ rho, receiverChannel (gdDilation v) (diagonal rho) = diagonal rho) ∧
    (∀ rho, diagonal (receiverChannel (gdDilation v) rho) = diagonal rho) ∧
    (∀ rho, complementaryChannel (gdDilation v) (diagonal rho) = complementaryChannel (gdDilation v) rho) ∧
    (∀ rho, complementaryChannel (gdDilation v) rho = ∑ i, rho i i • pureDensity (v i)) := by
  have hn : ∀ b, ∑ e, v b e * conj (v b e) = 1 := fun b => g79d_unit_sum _ (hv b)
  refine ⟨⟨hI, hI, inferInstance, ?_⟩, g79d_eb_prep _ v hv (g79d_gd_comp v), g79d_gd_recv_diag v hv,
    g79d_gd_diag_recv v hv, g79d_gd_comp_diag v, g79d_gd_comp v⟩
  unfold QAlgorithms.Papers.Independent.Information100.P67.IsIsometry
  ext i j
  simp only [gdDilation, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  by_cases h : i = j
  · subst h
    simp [g79d_conj_ite, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]
    rw [← hn i]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun e _ => ?_
    by_cases hb : b = i
    · subst hb; simp [h]
    · simp [hb]



end
