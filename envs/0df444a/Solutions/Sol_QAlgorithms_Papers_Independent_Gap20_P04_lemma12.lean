-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P04.lemma12
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:24:52.837719+00:00
-- url     : https://prove2.me/submissions/cd1937c4-613e-4a7c-9d4b-88b411f54343

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

lemma g79d_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma g79d_trace_cfc_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := g79d_diag_herm d
  rw [g79d_cfc_trace hD]
  have h1 := hD.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma g79d_vn_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [g79d_trace_cfc_diag]
  simp

lemma g79d_vn_eig {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) (hH : ρ.IsHermitian) :
    vnEntropy ρ = -∑ i, hH.eigenvalues i * Real.logb 2 (hH.eigenvalues i) := by
  unfold vnEntropy
  rw [g79d_cfc_trace hH]
  simp

lemma g79d_G_concave : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => -(x * Real.logb 2 x)) := by
  have h := (Real.concaveOn_negMulLog).smul (c := (Real.log 2)⁻¹)
    (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))
  refine h.congr (fun x _ => ?_)
  simp only [Real.negMulLog, Real.logb, smul_eq_mul]
  ring

lemma g79d_vn_le_diag {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ)
    (h : ρ.PosSemidef) :
    vnEntropy ρ ≤ vnEntropy (Matrix.diagonal (fun k => (((ρ k k).re : ℝ) : ℂ))) := by
  have hH := h.isHermitian
  set lam := hH.eigenvalues with hlam
  set V : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hV
  have hspec : ρ = V * Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)) * star V := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  set w : n → n → ℝ := fun k i => ‖V k i‖ ^ 2 with hw
  have hwc : ∀ k i, ((w k i : ℝ) : ℂ) = V k i * star (V k i) := by
    intro k i
    simp only [hw]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hkk : ∀ k, (ρ k k).re = ∑ i, w k i * lam i := by
    intro k
    have : ρ k k = ((∑ i, w k i * lam i : ℝ) : ℂ) := by
      conv_lhs => rw [hspec]
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.ofReal_sum, Complex.ofReal_mul, hwc]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, Complex.ofReal_re]
  have hrow : ∀ k, ∑ i, w k i = 1 := by
    intro k
    have h1 : V * star V = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
    have h2 := congrFun (congrFun h1 k) k
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h2
    have : ((∑ i, w k i : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← h2]
      exact Finset.sum_congr rfl fun i _ => hwc k i
    exact_mod_cast this
  have hcol : ∀ i, ∑ k, w k i = 1 := by
    intro i
    have h1 : star V * V = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    have h2 := congrFun (congrFun h1 i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h2
    have : ((∑ k, w k i : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← h2]
      exact Finset.sum_congr rfl fun k _ => by rw [hwc]; ring
    exact_mod_cast this
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => h.eigenvalues_nonneg i
  rw [g79d_vn_eig ρ hH, g79d_vn_diag]
  simp only [hkk]
  have hJ : ∀ k, ∑ i, w k i * (-(lam i * Real.logb 2 (lam i))) ≤
      -((∑ i, w k i * lam i) * Real.logb 2 (∑ i, w k i * lam i)) := by
    intro k
    have := g79d_G_concave.le_map_sum (t := Finset.univ) (w := w k) (p := lam)
      (fun i _ => by positivity) (hrow k) (fun i _ => Set.mem_Ici.mpr (hlam0 i))
    simpa [smul_eq_mul] using this
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hJ k)
  rw [Finset.sum_comm] at hsum
  have : ∑ i, ∑ k, w k i * (-(lam i * Real.logb 2 (lam i))) = ∑ i, (-(lam i * Real.logb 2 (lam i))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hcol i, one_mul]
  rw [this] at hsum
  simp only [Finset.sum_neg_distrib] at hsum
  linarith

lemma g79d_vn_le_dephase {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ)
    (h : ρ.PosSemidef) :
    vnEntropy ρ ≤ vnEntropy (QAlgorithms.Papers.Independent.Information100.P32.diagonal ρ) := by
  have e : QAlgorithms.Papers.Independent.Information100.P32.diagonal ρ =
      Matrix.diagonal (fun k => (((ρ k k).re : ℝ) : ℂ)) := by
    ext i j
    simp only [QAlgorithms.Papers.Independent.Information100.P32.diagonal, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij; exact (h.isHermitian.coe_re_apply_self i).symm
    · rfl
  rw [e]; exact g79d_vn_le_diag ρ h

lemma g79d_recv_psd {I B E : Type} [Fintype I] [Fintype B] [Fintype E]
    (U : Matrix (B × E) I ℂ) (ρ : Matrix I I ℂ) (h : ρ.PosSemidef) :
    (receiverChannel U ρ).PosSemidef := by
  have : receiverChannel U ρ = ∑ e : E, (Matrix.of fun (b : B) (i : I) => U (b, e) i) * ρ *
      (Matrix.of fun (b : B) (i : I) => U (b, e) i)ᴴ := by
    ext b c
    simp [receiverChannel, traceRight, Matrix.mul_apply, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ (fun e _ => h.mul_mul_conjTranspose_same _)

lemma g79d_ent_eq {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) :
    QAlgorithms.Papers.Independent.Information100.P56.entropy ρ = Real.log 2 * vnEntropy ρ := by
  have hc : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
    have := Real.continuous_mul_log.div_const (Real.log 2)
    convert this using 1
    funext x; simp only [Real.logb]; ring
  have hfun : (fun x : ℝ => x * Real.log x) = fun x => Real.log 2 * (x * Real.logb 2 x) := by
    funext x
    have : Real.log 2 ≠ 0 := by positivity
    simp only [Real.logb]; field_simp
  unfold QAlgorithms.Papers.Independent.Information100.P56.entropy vnEntropy
  rw [hfun, cfc_const_mul (Real.log 2) (fun x : ℝ => x * Real.logb 2 x) ρ hc.continuousOn,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  ring

lemma g79d_holevoBits {L H : Type} [Fintype L] [Fintype H] [DecidableEq H] (p : L → ℝ)
    (W : L → Matrix H H ℂ) :
    QAlgorithms.Papers.Independent.Dependency50.P24.ensembleHolevoBits p W =
      vnEntropy (∑ x, (p x : ℂ) • W x) - ∑ x, p x * vnEntropy (W x) := by
  unfold QAlgorithms.Papers.Independent.Dependency50.P24.ensembleHolevoBits
    QAlgorithms.Papers.Independent.Information100.P56.holevo
    QAlgorithms.Papers.Independent.Information100.P56.average
  simp only [g79d_ent_eq]
  have : Real.log 2 ≠ 0 := by positivity
  have key : ∀ (a : ℝ) (b : L → ℝ),
      (Real.log 2 * a - ∑ x, p x * (Real.log 2 * b x)) / Real.log 2 = a - ∑ x, p x * b x := by
    intro a b
    have h2 : ∑ x, p x * (Real.log 2 * b x) = Real.log 2 * ∑ x, p x * b x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    rw [h2]
    field_simp
  refine (key _ _).trans ?_
  congr!


/-- PDF p.21, Lemma 12: dephase input marginals and REPURIFY, with unchanged weights.
Arbitrary purifying reference dimensions are permitted on each side. -/
theorem solution (v : I → EuclideanSpace ℂ E) (hv : ∀ i, ‖v i‖ = 1)
    (e t : PurifiedInputFamily I) (he : e.Valid) (ht : t.Valid)
    (hreplace : DephasedReplacement e t) (lam : ℝ) (hlam : 1 ≤ lam) :
    cqScore (gdDilation v) lam e ≤ cqScore (gdDilation v) lam t := by
  obtain ⟨f, hf⟩ := hreplace
  have hin : ∀ x, (e.input x).PosSemidef := fun x => (g79d_tl_density _ (he.2.2.2.2 x)).1
  have hlin : ∀ (W : Fin e.labels → Matrix I I ℂ),
      receiverChannel (gdDilation v) (∑ x, (e.prob x : ℂ) • W x) =
        ∑ x, (e.prob x : ℂ) • receiverChannel (gdDilation v) (W x) := by
    intro W
    ext b c
    simp [g79d_gd_recv, Matrix.sum_apply, Finset.sum_mul, mul_assoc]
  have hT1 : (∑ y, (t.prob y : ℂ) • receiverChannel (gdDilation v) (t.input y)) =
      diagonal (receiverChannel (gdDilation v) e.average) := by
    rw [← Equiv.sum_comp f]
    simp only [(hf _).1, (hf _).2, g79d_gd_recv_diag v hv]
    rw [g79d_gd_diag_recv v hv]
    unfold PurifiedInputFamily.average
    ext i j
    simp only [diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hT2 : ∑ y, t.prob y * vnEntropy (receiverChannel (gdDilation v) (t.input y)) =
      ∑ x, e.prob x * vnEntropy (diagonal (receiverChannel (gdDilation v) (e.input x))) := by
    rw [← Equiv.sum_comp f]
    exact Finset.sum_congr rfl fun x _ => by
      rw [(hf x).1, (hf x).2, g79d_gd_recv_diag v hv, g79d_gd_diag_recv v hv]
  have hT3 : conditionalEnvironmentEntropy (gdDilation v) t =
      conditionalEnvironmentEntropy (gdDilation v) e := by
    unfold conditionalEnvironmentEntropy
    rw [← Equiv.sum_comp f]
    exact Finset.sum_congr rfl fun x _ => by rw [(hf x).1, (hf x).2, g79d_gd_comp_diag]
  have hE1 : (∑ x, (e.prob x : ℂ) • receiverChannel (gdDilation v) (e.input x)) =
      receiverChannel (gdDilation v) e.average := (hlin _).symm
  have hpsdavg : e.average.PosSemidef := by
    unfold PurifiedInputFamily.average
    exact Matrix.posSemidef_sum _ (fun x _ =>
      (hin x).smul (Complex.zero_le_real.mpr (he.2.2.1 x)))
  have h1 := g79d_vn_le_dephase _ (g79d_recv_psd (gdDilation v) _ hpsdavg)
  have h2 : ∑ x, e.prob x * vnEntropy (receiverChannel (gdDilation v) (e.input x)) ≤
      ∑ x, e.prob x * vnEntropy (diagonal (receiverChannel (gdDilation v) (e.input x))) :=
    Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (g79d_vn_le_dephase _ (g79d_recv_psd _ _ (hin x))) (he.2.2.1 x)
  have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ lam - 1)
  unfold cqScore ensembleCoherentBits conditionalReceiverEntropy
  rw [g79d_holevoBits, g79d_holevoBits, hT1, hT2, hT3, hE1]
  nlinarith



end
