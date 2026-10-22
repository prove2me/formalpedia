-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.cq_qc_complements
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:44:22.728412+00:00
-- url     : https://prove2.me/submissions/842871c0-67bb-4f35-ba3e-423d39532404

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

theorem g68l_kc1 (E : K → Matrix B A ℂ) :
    receiverChannel (indexedKrausDilation E) = krausApply E := by
  funext rho; ext b b'
  simp only [receiverChannel, traceRight, krausApply, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]

theorem g68l_kc2 (E : K → Matrix B A ℂ) (rho : Matrix A A ℂ) (a b : K) :
    complementaryChannel (indexedKrausDilation E) rho a b = (E a * rho * (E b)ᴴ).trace := by
  simp only [complementaryChannel, traceLeft, Matrix.trace, Matrix.diag, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]

theorem g68l_kc3 (E : K → Matrix B A ℂ) :
    complementaryChannel (indexedKrausDilation E) = krausApply (rowKraus E) := by
  funext rho; ext a b
  rw [g68l_kc2]
  simp only [krausApply, Matrix.trace, Matrix.diag, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]
theorem g68l_isChannel_of {ι κ K' : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype K']
    (E : K' → Matrix κ ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (Φ : Superop ι κ) (h : Φ = krausApply E) :
    IsChannel Φ := by
  refine ⟨Fintype.card K', fun i => E ((Fintype.equivFin K').symm i), ?_, fun rho => ?_⟩
  · unfold IsKrausFamily
    rw [← hE]
    exact Equiv.sum_comp (Fintype.equivFin K').symm (fun k => (E k)ᴴ * E k)
  · rw [h]
    exact (Equiv.sum_comp (Fintype.equivFin K').symm (fun k => E k * rho * (E k)ᴴ)).symm

theorem g68l_row_norm (E : K → Matrix B A ℂ) :
    ∑ b, (rowKraus E b)ᴴ * rowKraus E b = ∑ k, (E k)ᴴ * E k := by
  ext a a'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]
  exact Finset.sum_comm

theorem g68l_tr {ι A' B' : Type*} [Fintype ι] [Fintype A'] [Fintype B'] (F : ι → Matrix B' A' ℂ)
    (ρ : Matrix A' A' ℂ) :
    ((∑ j, (F j)ᴴ * F j) * ρ).trace = ∑ j, (F j * ρ * (F j)ᴴ).trace := by
  rw [Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

theorem g68l_inner (x y : EuclideanSpace ℂ B) : inner ℂ x y = ∑ i, conj (x i) * y i := by
  rw [PiLp.inner_apply]; simp [mul_comm]

theorem g68l_ch_tp {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (Φ : Superop ι κ)
    (h : IsChannel Φ) (ρ : Matrix ι ι ℂ) : (Φ ρ).trace = ρ.trace := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  rw [hΦ ρ]
  simp only [krausApply, Matrix.trace_sum]
  rw [← g68l_tr, hE, Matrix.one_mul]

theorem g68l_eb_comp (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    complementaryChannel (indexedKrausDilation (rankOneKraus psi phi)) =
      arbitraryVectorComplement (gram phi) psi := by
  funext rho; ext a b
  rw [g68l_kc2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, rankOneKraus,
    arbitraryVectorComplement, gram, g68l_inner, Finset.sum_mul, Finset.mul_sum, RCLike.star_def, map_mul,
    Complex.conj_conj]
  simp only [← Fintype.sum_prod_type']
  let e : (B × A × A) ≃ (A × A × B) :=
    { toFun := fun x => (x.2.2, x.2.1, x.1)
      invFun := fun y => (y.2.2, y.2.1, y.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ (fun x => ?_)
  simp only [e, Equiv.coe_fn_mk]; ring

theorem g68l_eb_cp (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    CPComplementary (krausApply (rankOneKraus psi phi)) (arbitraryVectorComplement (gram phi) psi) :=
  ⟨indexedKrausDilation (rankOneKraus psi phi), g68l_kc1 _, g68l_eb_comp psi phi⟩

/-- PDF p.5: c-q is the pure-preparation subclass; q-c is the same diagonal
measurement map after identifying the two output bases. -/
theorem solution [Nonempty A]
    (U : Matrix.unitaryGroup A ℂ) (phi : A → EuclideanSpace ℂ B) :
    (∀ rho, arbitraryVectorComplement (gram phi) (basisColumns U) rho =
      Matrix.hadamard (gram phi) ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ))) ∧
    CPComplementary (krausApply (rankOneKraus (basisColumns U) phi)) (arbitraryVectorComplement (gram phi) (basisColumns U)) ∧
    (IsChannel (arbitraryVectorComplement (gram phi) (basisColumns U)) ↔ ∀ a, gram phi a a = 1) ∧
    (∀ (psi : B → EuclideanSpace ℂ A) (W : Matrix.unitaryGroup B ℂ),
      gram (basisColumns W) = 1 ∧
      (∀ rho, krausApply (rankOneKraus psi (basisColumns W)) rho =
        (W : Matrix B B ℂ) * arbitraryVectorComplement 1 psi rho * (W : Matrix B B ℂ)ᴴ) ∧
      CPComplementary (krausApply (rankOneKraus psi (basisColumns W))) (arbitraryVectorComplement 1 psi)) := by
  have h1 : ∀ rho, arbitraryVectorComplement (gram phi) (basisColumns U) rho =
      Matrix.hadamard (gram phi) ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ)) := by
    intro rho; ext a b
    simp only [arbitraryVectorComplement, Matrix.hadamard, Matrix.mul_apply, Matrix.conjTranspose_apply,
      basisColumns, RCLike.star_def, Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  refine ⟨h1, g68l_eb_cp _ _, ⟨fun hch a => ?_, fun hg => ?_⟩, fun psi W => ?_⟩
  · have hU' : (U : Matrix A A ℂ)ᴴ * (U : Matrix A A ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
    have := g68l_ch_tp _ hch ((U : Matrix A A ℂ) * Matrix.single a a 1 * (U : Matrix A A ℂ)ᴴ)
    rw [h1] at this
    have e1 : (U : Matrix A A ℂ)ᴴ * ((U : Matrix A A ℂ) * Matrix.single a a 1 * (U : Matrix A A ℂ)ᴴ) *
        (U : Matrix A A ℂ) = Matrix.single a a 1 := by
      simp only [← Matrix.mul_assoc, hU', Matrix.one_mul]
      rw [Matrix.mul_assoc, hU', Matrix.mul_one]
    rw [e1, Matrix.trace_mul_cycle, hU', Matrix.one_mul] at this
    simpa [Matrix.trace, Matrix.hadamard, Matrix.single_apply] using this
  · have hU : (U : Matrix A A ℂ) * (U : Matrix A A ℂ)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
    rw [← g68l_eb_comp, g68l_kc3]
    refine g68l_isChannel_of _ ?_ _ rfl
    rw [g68l_row_norm, ← hU]
    ext i i'
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, rankOneKraus, basisColumns,
      RCLike.star_def, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hg k
    simp only [gram, g68l_inner] at this
    calc _ = (∑ x, (starRingEnd ℂ) ((phi k).ofLp x) * (phi k).ofLp x) *
          ((U : Matrix A A ℂ) i k * (starRingEnd ℂ) ((U : Matrix A A ℂ) i' k)) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [this, one_mul]
  · have hW' : (W : Matrix B B ℂ)ᴴ * (W : Matrix B B ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp W.2
    have hg : gram (basisColumns W) = 1 := by
      ext a b
      have := congrFun (congrFun hW' b) a
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def] at this
      simp only [gram, g68l_inner, basisColumns, Matrix.one_apply] at this ⊢
      rw [this]; by_cases h : a = b <;> simp [h, eq_comm]
    refine ⟨hg, fun rho => ?_, ?_⟩
    · ext x y
      simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, rankOneKraus,
        basisColumns, arbitraryVectorComplement, Matrix.one_apply, RCLike.star_def, map_mul, Complex.conj_conj,
        ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
      simp only [if_true]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · have := g68l_eb_cp psi (basisColumns W)
      rwa [hg] at this



end
