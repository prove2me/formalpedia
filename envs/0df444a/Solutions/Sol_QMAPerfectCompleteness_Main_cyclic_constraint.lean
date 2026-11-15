-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.cyclic_constraint
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T12:17:37.110558+00:00
-- url     : https://prove2.me/submissions/a36d1859-6cb3-4c61-b3ff-f9ad9fac4066

import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic

set_option autoImplicit false

/- Flattened from Solutions.EuclideanStates -/
section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QMAPerfectCompleteness.Main.VerifierAnalysis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma euclidNorm_nonneg (v : ι → ℂ) : 0 ≤ euclidNorm v := Real.sqrt_nonneg _

lemma euclidNorm_sq (v : ι → ℂ) : euclidNorm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma euclidNorm_smul (c : ℂ) (v : ι → ℂ) :
    euclidNorm (c • v) = ‖c‖ * euclidNorm v := by
  simp only [euclidNorm, Pi.smul_apply, norm_smul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma euclidNorm_eq_zero_iff (v : ι → ℂ) : euclidNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hs : ∑ i, ‖v i‖ ^ 2 = 0 := by rw [← euclidNorm_sq, h]; norm_num
    funext i
    have hi : ‖v i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hs i (Finset.mem_univ i)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (v i)])
  · rintro rfl
    simp [euclidNorm]

lemma euclidNorm_pos (v : ι → ℂ) (hv : v ≠ 0) : 0 < euclidNorm v := by
  exact lt_of_le_of_ne (euclidNorm_nonneg v) (Ne.symm (mt (euclidNorm_eq_zero_iff v).mp hv))

/-- Normalize using the Euclidean norm, rather than the sup norm of a function type. -/
noncomputable def normalize (v : ι → ℂ) : ι → ℂ := ((euclidNorm v : ℂ)⁻¹) • v

lemma normalize_euclidNorm (v : ι → ℂ) (hv : v ≠ 0) : euclidNorm (normalize v) = 1 := by
  rw [normalize, euclidNorm_smul]
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (euclidNorm_nonneg v), ne_of_gt (euclidNorm_pos v hv)]

lemma normalize_kernel (B : Matrix κ ι ℂ) (v : ι → ℂ) (h : B *ᵥ v = 0) :
    B *ᵥ normalize v = 0 := by
  simp [normalize, Matrix.mulVec_smul, h]

/-- The rank-one matrix |v⟩⟨v|. -/
def pureDensity (v : ι → ℂ) : Matrix ι ι ℂ := vecMulVec v (star v)

lemma pureDensity_posSemidef (v : ι → ℂ) : (pureDensity v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

lemma pureDensity_trace [DecidableEq ι] (v : ι → ℂ) :
    (pureDensity v).trace = ((euclidNorm v ^ 2 : ℝ) : ℂ) := by
  rw [pureDensity, Matrix.trace_vecMulVec, euclidNorm_sq]
  simp [dotProduct, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma pureDensity_trace_one [DecidableEq ι] (v : ι → ℂ) (hv : euclidNorm v = 1) :
    (pureDensity v).trace = 1 := by rw [pureDensity_trace, hv]; norm_num

lemma pureDensity_expectation [DecidableEq ι] (E : Matrix ι ι ℂ) (v : ι → ℂ) :
    (E * pureDensity v).trace = star v ⬝ᵥ (E *ᵥ v) := by
  rw [pureDensity, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- Squared norm as the quadratic form of a Gram matrix. -/
lemma gram_expectation [DecidableEq ι] (B : Matrix κ ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ ((Bᴴ * B) *ᵥ v) = ((euclidNorm (B *ᵥ v) ^ 2 : ℝ) : ℂ) := by
  classical
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose,
    star_star, dotProduct_comm]
  simpa [pureDensity, Matrix.trace_vecMulVec] using pureDensity_trace (B *ᵥ v)

/-- The trace pairing of positive matrices is nonnegative even when they do not commute. -/
lemma trace_mul_posSemidef_nonneg [DecidableEq ι] (A R : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hR : R.PosSemidef) : 0 ≤ (A * R).trace.re := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  have hp := (hA.mul_mul_conjTranspose_same S).trace_nonneg
  have ht : (S * A * Sᴴ).trace = (A * (star S * S)).trace := by
    rw [Matrix.trace_mul_cycle, star_eq_conjTranspose, Matrix.trace_mul_comm]
  rw [ht] at hp
  exact (Complex.nonneg_iff.mp hp).1

/-- A uniform quadratic-form bound extends to every density matrix. -/
lemma mixed_bound_of_quadratic [DecidableEq ι] (E : Matrix ι ι ℂ) (q : ℝ)
    (hE : E.IsHermitian)
    (hq : ∀ v : ι → ℂ, q * euclidNorm v ^ 2 ≤ (star v ⬝ᵥ (E *ᵥ v)).re)
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    q ≤ (E * ρ).trace.re := by
  have hpos : (E - (q : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact hE.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint (q : ℂ) from by simp [IsSelfAdjoint]))
    · intro v
      apply Complex.nonneg_iff.mpr
      constructor
      · have hv := hq v
        have hs : star v ⬝ᵥ v = ((euclidNorm v ^ 2 : ℝ) : ℂ) := by
          rw [dotProduct_comm]
          simpa [pureDensity, Matrix.trace_vecMulVec] using pureDensity_trace v
        simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
          dotProduct_smul, hs, ← Complex.ofReal_pow] using sub_nonneg.mpr hv
      · exact ((hE.sub (Matrix.isHermitian_one.smul (show IsSelfAdjoint (q : ℂ) from by simp [IsSelfAdjoint]))).im_star_dotProduct_mulVec_self v).symm
  have hp := trace_mul_posSemidef_nonneg _ ρ hpos hρ
  simpa [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    htrace] using hp

end QMAPerfectCompleteness.Main.VerifierAnalysis
end


/- Flattened from Solutions.Cyclic -/
section

open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CyclicProof

variable {G : GateSet}

theorem history_ne_zero (V : Verifier G) (z : V.Proof) : V.historyVector z ≠ 0 := by
  intro h
  have h0 := congrFun h (0, z)
  simp [Verifier.historyVector] at h0

theorem acceptance_hermitian (V : Verifier G) : V.acceptanceOperator.IsHermitian := by
  have hP : V.acceptProjector.IsHermitian := by
    unfold Verifier.acceptProjector
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    ext w
    simp only [Pi.star_apply]
    split <;> simp
  have h := Matrix.isHermitian_conjTranspose_mul_mul (V.unitary * V.ancillaZero) hP
  simpa only [Verifier.acceptanceOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

theorem doubled_hermitian (V : Verifier G) : V.doubled.IsHermitian := by
  exact (acceptance_hermitian V).smul (by norm_num : IsSelfAdjoint (2 : ℂ))

theorem gamma_eq_diagonal (V : Verifier G) (z : V.Proof) :
    (V.gamma z : ℂ) = (V.doubled ^ ell V.proofQubits) z z := by
  have h := (doubled_hermitian V).pow (ell V.proofQubits)
  have hz := congrArg (fun M : Matrix V.Proof V.Proof ℂ => (M z z).im) h.eq
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at hz
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

theorem single_kronecker_mulVec {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (a b t : α) (p : β) (A : Matrix β β ℂ)
    (v : α × β → ℂ) :
    (((Matrix.single a b (1 : ℂ)) ⊗ₖ A) *ᵥ v) (t,p) =
      if t = a then (A *ᵥ fun q => v (b,q)) p else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.single_apply]
  by_cases h : t = a
  · subst t
    simp
  · simp [h, Ne.symm h]

theorem cyclic_mulVec_zero (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (v : History V → ℂ) (p : V.Proof) :
    (V.cyclicOp z Γ *ᵥ v) (0,p) =
      if p = z then (Γ⁻¹ : ℂ) * v (Fin.last (ell V.proofQubits),z) else 0 := by
  classical
  simp only [Verifier.cyclicOp, Matrix.add_mulVec, Matrix.sum_mulVec, Pi.add_apply,
    Finset.sum_apply, single_kronecker_mulVec]
  simp [Matrix.single_mulVec_eq, Fin.succ_ne_zero, Pi.single_apply, eq_comm]

theorem cyclic_mulVec_succ (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (v : History V → ℂ) (t : Fin (ell V.proofQubits)) (p : V.Proof) :
    (V.cyclicOp z Γ *ᵥ v) (t.succ,p) =
      (V.doubled *ᵥ fun q => v (t.castSucc,q)) p := by
  classical
  simp only [Verifier.cyclicOp, Matrix.add_mulVec, Matrix.sum_mulVec, Pi.add_apply,
    Finset.sum_apply, single_kronecker_mulVec]
  simp [Fin.succ_ne_zero]

/-- The cycle permutes the history summands exactly when its closing coefficient is honest. -/
theorem history_fixed (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (hΓ : Γ = V.gamma z) (hΓ0 : Γ ≠ 0) :
    V.cyclicOp z Γ *ᵥ V.historyVector z = V.historyVector z := by
  classical
  funext x
  obtain ⟨t,p⟩ := x
  refine Fin.cases ?_ (fun t => ?_) t
  · rw [cyclic_mulVec_zero]
    by_cases hp : p = z
    · subst p
      simp only [if_pos rfl, Verifier.historyVector, Fin.val_last, Fin.val_zero, pow_zero,
        Matrix.one_apply_eq]
      rw [← gamma_eq_diagonal V z, ← hΓ]
      simp [hΓ0]
    · simp [hp, Verifier.historyVector, eq_comm]
  · rw [cyclic_mulVec_succ]
    simp only [Verifier.historyVector, Fin.val_castSucc, Fin.val_succ, pow_succ',
      Matrix.mulVec, dotProduct, Matrix.mul_apply]

/-- Lemma 3.4(i), stronger than stated: the YES hypothesis is unnecessary once Γ is honest. -/
theorem history_kernel (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (hgamma : 2 < V.gamma z) (hΓ : Γ = V.gamma z) :
    V.historyVector z ≠ 0 ∧ (1 - V.cyclicOp z Γ) *ᵥ V.historyVector z = 0 := by
  refine ⟨history_ne_zero V z, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec,
    history_fixed V z Γ hΓ (by rw [hΓ]; linarith)]
  exact sub_self _

theorem cyclicOp_apply_zero (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (s : Clock V.proofQubits) (p q : V.Proof) :
    V.cyclicOp z Γ (0,p) (s,q) =
      if p = z ∧ s = Fin.last (ell V.proofQubits) ∧ q = z then ((Γ⁻¹ : ℝ) : ℂ) else 0 := by
  classical
  have h := cyclic_mulVec_zero V z Γ (Pi.single (s,q) 1) p
  simp only [Matrix.mulVec_single_one] at h
  by_cases hp : p = z <;> by_cases hs : s = Fin.last (ell V.proofQubits) <;>
    by_cases hq : q = z <;>
    simp_all [Pi.single_apply, Prod.mk.injEq]

theorem cyclicOp_apply_succ (V : Verifier G) (z : V.Proof) (Γ : ℝ)
    (t : Fin (ell V.proofQubits)) (s : Clock V.proofQubits) (p q : V.Proof) :
    V.cyclicOp z Γ (t.succ,p) (s,q) =
      if s = t.castSucc then V.doubled p q else 0 := by
  classical
  have h := cyclic_mulVec_succ V z Γ (Pi.single (s,q) 1) t p
  simp only [Matrix.mulVec_single_one] at h
  by_cases hs : s = t.castSucc
  · subst s
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Prod.mk.injEq, eq_comm] using h
  · simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Prod.mk.injEq, hs, Ne.symm hs] using h

open VerifierAnalysis

/-- The Euclidean triangle inequality, avoiding the sup norm on function types. -/
theorem euclidNorm_le_sub_add {ι : Type*} [Fintype ι] (v w : ι → ℂ) :
    euclidNorm v ≤ euclidNorm (v - w) + euclidNorm w := by
  have h := norm_add_le (WithLp.toLp 2 (v-w) : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 w : EuclideanSpace ℂ ι)
  simpa only [← WithLp.toLp_add, sub_add_cancel, EuclideanSpace.norm_eq,
    PiLp.toLp_apply, euclidNorm] using h

/-- A contraction by 2/3 gives the paper's 1/3 lower bound for I-C. -/
theorem gap_of_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) (hC : ∀ v, euclidNorm (C *ᵥ v) ≤ (2 / 3) * euclidNorm v)
    (v : ι → ℂ) : (1 / 3) * euclidNorm v ≤ euclidNorm ((1-C) *ᵥ v) := by
  have ht := euclidNorm_le_sub_add v (C *ᵥ v)
  have hc := hC v
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  linarith

/-- Squared norm of the rank-one closing transition is at most 4/9 times its input norm. -/
theorem closing_sq_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι) (Γ : ℝ) (hΓ : 2 ≤ Γ) (v : ι → ℂ) :
    (∑ p, ‖(if p = z then ((Γ⁻¹ : ℝ) : ℂ) * v z else 0)‖ ^ 2) ≤
      (4 / 9 : ℝ) * ∑ p, ‖v p‖ ^ 2 := by
  classical
  have hg : 0 < Γ := by linarith
  have hr : ‖((Γ⁻¹ : ℝ) : ℂ)‖ ≤ (2 / 3 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hg.le)]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hΓ
    simp only [one_div] at hi
    linarith
  have hr2 : ‖((Γ⁻¹ : ℝ) : ℂ)‖ ^ 2 ≤ (4 / 9 : ℝ) := by
    nlinarith [norm_nonneg (((Γ⁻¹ : ℝ) : ℂ))]
  have hz : ‖v z‖ ^ 2 ≤ ∑ p, ‖v p‖ ^ 2 :=
    Finset.single_le_sum (fun p _ => sq_nonneg ‖v p‖) (Finset.mem_univ z)
  have heq : (∑ p, ‖(if p = z then ((Γ⁻¹ : ℝ) : ℂ) * v z else 0)‖ ^ 2) =
      ‖((Γ⁻¹ : ℝ) : ℂ)‖ ^ 2 * ‖v z‖ ^ 2 := by
    simp [apply_ite, norm_mul, mul_pow]
  rw [heq]
  exact mul_le_mul hr2 hz (sq_nonneg _) (by norm_num)

/-- The cyclic shift has disjoint output blocks, so blockwise contraction implies contraction
of the whole history. This is the norm argument in Eq. (4), written as a sum of squared norms. -/
theorem cyclic_contraction (V : Verifier G) (z : V.Proof) (Γ : ℝ) (hΓ : 2 ≤ Γ)
    (hA : ∀ v : V.Proof → ℂ,
      euclidNorm (V.doubled *ᵥ v) ≤ (2 / 3) * euclidNorm v) :
    ∀ v : History V → ℂ,
      euclidNorm (V.cyclicOp z Γ *ᵥ v) ≤ (2 / 3) * euclidNorm v := by
  intro v
  have hAsq (t : Fin (ell V.proofQubits)) :
      (∑ p, ‖(V.doubled *ᵥ fun q => v (t.castSucc,q)) p‖ ^ 2) ≤
        (4 / 9 : ℝ) * ∑ p, ‖v (t.castSucc,p)‖ ^ 2 := by
    have h := hA (fun q => v (t.castSucc,q))
    have hn := euclidNorm_nonneg (V.doubled *ᵥ fun q => v (t.castSucc,q))
    have hv := euclidNorm_nonneg (fun q => v (t.castSucc,q))
    rw [← euclidNorm_sq, ← euclidNorm_sq]
    nlinarith
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hAsq t)
  have hc := closing_sq_bound z Γ hΓ (fun p => v (Fin.last (ell V.proofQubits),p))
  simp only [Complex.ofReal_inv] at hc
  have htotal : euclidNorm (V.cyclicOp z Γ *ᵥ v) ^ 2 ≤
      (4 / 9 : ℝ) * euclidNorm v ^ 2 := by
    rw [euclidNorm_sq, euclidNorm_sq]
    simp only [Fintype.sum_prod_type]
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc (fun t => ∑ p, ‖v (t,p)‖ ^ 2)]
    simp only [cyclic_mulVec_zero, cyclic_mulVec_succ]
    rw [← Finset.mul_sum] at hs
    linarith
  have hn := euclidNorm_nonneg (V.cyclicOp z Γ *ᵥ v)
  have hv := euclidNorm_nonneg v
  nlinarith

/-- The soundness clause, with only the acceptance-operator contraction left as a hypothesis. -/
theorem cyclic_gap_of_doubled_contraction (V : Verifier G)
    (hA : ∀ v : V.Proof → ℂ,
      euclidNorm (V.doubled *ᵥ v) ≤ (2 / 3) * euclidNorm v)
    (z : V.Proof) (Γ : ℝ) (hΓ : 2 ≤ Γ) (v : History V → ℂ) :
    (1 / 3) * euclidNorm v ≤ euclidNorm ((1 - V.cyclicOp z Γ) *ᵥ v) := by
  exact gap_of_contraction _ (cyclic_contraction V z Γ hΓ hA) v

open scoped ComplexOrder

/-- Positivity of the acceptance operator follows directly from its compression formula. -/
theorem acceptance_posSemidef (V : Verifier G) : V.acceptanceOperator.PosSemidef := by
  have hp : V.acceptProjector.PosSemidef := by
    unfold Verifier.acceptProjector
    apply Matrix.PosSemidef.diagonal
    intro w
    change 0 ≤ (if w V.output then (1 : ℂ) else 0)
    split <;> simp
  have h := hp.conjTranspose_mul_mul_same (V.unitary * V.ancillaZero)
  simpa only [Verifier.acceptanceOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

/-- Soundness bounds every eigenvalue, using a normalized pure eigenstate as the proof. -/
theorem acceptance_eigenvalue_le (V : Verifier G)
    (hno : V.AcceptsAllProofsAtMost (1 / 3)) (i : V.Proof) :
    (acceptance_hermitian V).eigenvalues i ≤ (1 / 3 : ℝ) := by
  let h := acceptance_hermitian V
  let v : V.Proof → ℂ := ⇑(h.eigenvectorBasis i)
  have hv : euclidNorm v = 1 := by
    have hv := h.eigenvectorBasis.orthonormal.1 i
    simpa only [EuclideanSpace.norm_eq, euclidNorm, v] using hv
  have hb := hno (pureDensity v) ⟨pureDensity_posSemidef v, pureDensity_trace_one v hv⟩
  change (V.acceptanceOperator * pureDensity v).trace.re ≤ (1 / 3 : ℝ) at hb
  rw [pureDensity_expectation] at hb
  rw [h.eigenvalues_eq]
  exact hb

open scoped Matrix.Norms.L2Operator

/-- The spectral theorem turns the eigenvalue interval [0,1/3] into a Euclidean operator bound. -/
theorem acceptance_opNorm_le (V : Verifier G)
    (hno : V.AcceptsAllProofsAtMost (1 / 3)) : ‖V.acceptanceOperator‖ ≤ (1 / 3 : ℝ) := by
  let h := acceptance_hermitian V
  rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)).2
  intro i
  change ‖((h.eigenvalues i : ℝ) : ℂ)‖ ≤ (1 / 3 : ℝ)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((acceptance_posSemidef V).eigenvalues_nonneg i)]
  exact acceptance_eigenvalue_le V hno i

/-- The NO-instance hypothesis gives precisely the contraction used in the paper. -/
theorem doubled_contraction (V : Verifier G) (hno : V.AcceptsAllProofsAtMost (1 / 3))
    (v : V.Proof → ℂ) :
    euclidNorm (V.doubled *ᵥ v) ≤ (2 / 3) * euclidNorm v := by
  have hn : ‖V.doubled‖ ≤ (2 / 3 : ℝ) := by
    rw [Verifier.doubled, norm_smul]
    norm_num
    linarith [acceptance_opNorm_le V hno]
  have hv := Matrix.l2_opNorm_mulVec V.doubled (WithLp.toLp 2 v)
  have heq (w : V.Proof → ℂ) : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ V.Proof)‖ = euclidNorm w := by
    rw [EuclideanSpace.norm_eq]
    rfl
  change ‖(WithLp.toLp 2 (V.doubled *ᵥ v) : EuclideanSpace ℂ V.Proof)‖ ≤
    ‖V.doubled‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ V.Proof)‖ at hv
  rw [heq, heq] at hv
  exact hv.trans (mul_le_mul_of_nonneg_right hn (euclidNorm_nonneg v))

/-- Lemma 3.4, proved without importing its platform placeholder. -/
theorem cyclic_constraint (V : Verifier gatesG2) :
    (V.AcceptsSomeProof (2 / 3) → ∀ (z : V.Proof) (Γ : ℝ), 2 < V.gamma z → Γ = V.gamma z →
      V.historyVector z ≠ 0 ∧ (1 - V.cyclicOp z Γ) *ᵥ V.historyVector z = 0) ∧
    (V.AcceptsAllProofsAtMost (1 / 3) → ∀ (z : V.Proof) (Γ : ℝ), 2 ≤ Γ → ∀ Ψ : History V → ℂ,
      (1 / 3) * euclidNorm Ψ ≤ euclidNorm ((1 - V.cyclicOp z Γ) *ᵥ Ψ)) := by
  constructor
  · intro _ z Γ hgamma hΓ
    exact history_kernel V z Γ hgamma hΓ
  · intro hno z Γ hΓ Ψ
    exact cyclic_gap_of_doubled_contraction V (doubled_contraction V hno) z Γ hΓ Ψ

end QMAPerfectCompleteness.Main.CyclicProof
end


open Matrix QMAPerfectCompleteness.Main

/-- Lemma 3.4 (p. 8). (i) On a YES instance, if `Γ_z > 2` and `Γ = Γ_z`, then `|Ω_z⟩ ≠ 0` satisfies
`(I - C_{z,Γ})|Ω_z⟩ = 0`. (ii) On a NO instance (`E ⪯ I/3`),
`‖(I - C_{z,Γ})|Ψ⟩‖ ≥ (1/3)‖|Ψ⟩‖` for all `z`, all `Γ ≥ 2` and all `|Ψ⟩`. -/
theorem solution (V : Verifier gatesG2) :
    (V.AcceptsSomeProof (2 / 3) → ∀ (z : V.Proof) (Γ : ℝ), 2 < V.gamma z → Γ = V.gamma z →
      V.historyVector z ≠ 0 ∧ (1 - V.cyclicOp z Γ) *ᵥ V.historyVector z = 0) ∧
    (V.AcceptsAllProofsAtMost (1 / 3) → ∀ (z : V.Proof) (Γ : ℝ), 2 ≤ Γ → ∀ Ψ : History V → ℂ,
      (1 / 3) * euclidNorm Ψ ≤ euclidNorm ((1 - V.cyclicOp z Γ) *ᵥ Ψ)) := by
  exact QMAPerfectCompleteness.Main.CyclicProof.cyclic_constraint V

#print axioms solution
