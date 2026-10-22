-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.dual_stinespring
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:23:13.712214+00:00
-- url     : https://prove2.me/submissions/9ace8ec7-ce72-4aa1-841c-2e7e22d260c2

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

theorem g68l_rc_entry {B' C' A' : Type*} [Fintype B'] [Fintype C'] [Fintype A']
    (V : Matrix (B' × C') A' ℂ) (X : Matrix A' A' ℂ) (b b' : B') :
    receiverChannel V X b b' = ∑ k, ∑ i, ∑ j, V (b,k) i * X i j * conj (V (b',k) j) := by
  simp only [receiverChannel, traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem g68l_cc_entry {B' C' A' : Type*} [Fintype B'] [Fintype C'] [Fintype A']
    (V : Matrix (B' × C') A' ℂ) (X : Matrix A' A' ℂ) (k k' : C') :
    complementaryChannel V X k k' = ∑ b, ∑ i, ∑ j, V (b,k) i * X i j * conj (V (b,k') j) := by
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem g68l_rc_single {B' C' A' : Type*} [Fintype B'] [Fintype C'] [Fintype A'] [DecidableEq A']
    (V : Matrix (B' × C') A' ℂ) (a c : A') (b b' : B') :
    receiverChannel V (Matrix.single a c 1) b b' = ∑ k, V (b,k) a * conj (V (b',k) c) := by
  rw [g68l_rc_entry]
  simp [Matrix.single_apply, ite_and]

theorem g68l_kc1 (E : K → Matrix B A ℂ) :
    receiverChannel (indexedKrausDilation E) = krausApply E := by
  funext rho; ext b b'
  simp only [receiverChannel, traceRight, krausApply, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, indexedKrausDilation, Fintype.sum_prod_type]


theorem g68l_rc_lin {B' C' A' : Type*} [Fintype B'] [Fintype C'] [Fintype A'] [DecidableEq A']
    (V : Matrix (B' × C') A' ℂ) (rho : Matrix A' A' ℂ) :
    receiverChannel V rho = ∑ a, ∑ b, rho a b • receiverChannel V (Matrix.single a b 1) := by
  ext x y
  rw [g68l_rc_entry]
  simp only [Matrix.sum_apply, Matrix.smul_apply, g68l_rc_single, smul_eq_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  let e : (C' × A' × A') ≃ (A' × A' × C') :=
    { toFun := fun x => (x.2.1, x.2.2, x.1)
      invFun := fun y => (y.2.2, y.1, y.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ (fun x => ?_)
  simp only [e, Equiv.coe_fn_mk]; ring

theorem g68l_dual_pair {B' A' : Type*} [Fintype B'] [Fintype A'] [DecidableEq A']
    (Phi : Superop A' B') (hlin : ∀ rho, Phi rho = ∑ a, ∑ b, rho a b • Phi (Matrix.single a b 1))
    (rho : Matrix A' A' ℂ) (X : Matrix B' B' ℂ) :
    (Phi rho * X).trace = (rho * operatorTraceDual Phi X).trace := by
  rw [hlin rho]
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, operatorTraceDual, Finset.sum_apply]

theorem g68l_trace_ext {B' : Type*} [Fintype B'] [DecidableEq B'] (M N : Matrix B' B' ℂ)
    (h : ∀ X : Matrix B' B' ℂ, (M * X).trace = (N * X).trace) : M = N := by
  ext i j
  have := h (Matrix.single j i 1)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero,
    ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact this

theorem g68l_dual_rc {B' C' A' : Type*} [Fintype B'] [Fintype C'] [Fintype A'] [DecidableEq A']
    [DecidableEq C'] (V : Matrix (B' × C') A' ℂ) (X : Matrix B' B' ℂ) :
    operatorTraceDual (receiverChannel V) X = Vᴴ * (X ⊗ₖ (1 : Matrix C' C' ℂ)) * V := by
  ext a b
  simp only [operatorTraceDual, g68l_rc_single, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    RCLike.star_def, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  let e : (B' × B' × C') ≃ (B' × C' × B') :=
    { toFun := fun x => (x.1, x.2.2, x.2.1)
      invFun := fun y => (y.1, y.2.2, y.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ (fun x => ?_)
  simp only [e, Equiv.coe_fn_mk]; ring

/-- Equation (21), PDF pp.10–11: computed trace-dual, trace pairing,
and equivalence with the Schroedinger partial-trace formula. -/
theorem solution [Nonempty A] (Phi : Superop A B) (hPhi : FiniteKrausCP Phi)
    (V : Matrix (B × C) A ℂ) :
    (∀ rho X, (Phi rho * X).trace = (rho * operatorTraceDual Phi X).trace) ∧
    ((∀ rho, Phi rho = receiverChannel V rho) ↔
      ∀ X, operatorTraceDual Phi X = Vᴴ * (X ⊗ₖ (1 : Matrix C C ℂ)) * V) := by
  obtain ⟨r, E, rfl⟩ := hPhi
  have hlinK : ∀ rho, krausApply E rho = ∑ a, ∑ b, rho a b • krausApply E (Matrix.single a b 1) := by
    rw [← g68l_kc1]; exact g68l_rc_lin _
  refine ⟨g68l_dual_pair _ hlinK, ⟨fun h X => ?_, fun h rho => ?_⟩⟩
  · rw [← g68l_dual_rc]
    have : krausApply E = receiverChannel V := funext h
    rw [this]
  · apply g68l_trace_ext
    intro X
    rw [g68l_dual_pair _ hlinK, g68l_dual_pair _ (g68l_rc_lin V), h X, g68l_dual_rc]



end
