-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.assisted_independence_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:36:53.493716+00:00
-- url     : https://prove2.me/submissions/0fd9ecc6-4c17-4637-b3e1-dde979a59d34

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_assisted_message_dimension_bound

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

private lemma trace_pull {A B : Type} [Fintype A] [Fintype B]
    (L : Matrix B A ℂ) (D : Matrix A A ℂ) (X : Matrix B B ℂ) :
    Matrix.trace ((L * D * Lᴴ)ᴴ * X) = Matrix.trace (Dᴴ * (Lᴴ * X * L)) := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

private abbrev liftEncoding {I J E R : Type} [Fintype I] [Fintype J]
    [Fintype E] [Fintype R] [DecidableEq R]
    (V : Matrix (J × E) I ℂ) : Matrix (J × (E × R)) (I × R) ℂ :=
  (V ⊗ₖ (1 : Matrix R R ℂ)).submatrix (Equiv.prodAssoc J E R).symm id

private lemma lift_isometry {I J E R : Type} [Fintype I] [Fintype J]
    [Fintype E] [Fintype R] [DecidableEq I] [DecidableEq R]
    (V : Matrix (J × E) I ℂ) (hV : Vᴴ * V = 1) :
    (liftEncoding (R := R) V)ᴴ * liftEncoding (R := R) V = 1 := by
  rw [liftEncoding, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, hV, Matrix.one_mul, Matrix.one_kronecker_one]

private lemma lift_compress_single {I J E R : Type} [Fintype I] [Fintype J]
    [Fintype E] [Fintype R] [DecidableEq I] [DecidableEq J]
    [DecidableEq E] [DecidableEq R]
    (V : Matrix (J × E) I ℂ) (X : Matrix J J ℂ) (a b : E) (s t : R) (z : ℂ) :
    (liftEncoding (R := R) V)ᴴ * (X ⊗ₖ Matrix.single (a,s) (b,t) z) * liftEncoding (R := R) V =
      (Vᴴ * (X ⊗ₖ Matrix.single a b 1) * V) ⊗ₖ Matrix.single s t z := by
  ext ⟨i,u⟩ ⟨k,v⟩
  simp [liftEncoding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.single_apply, Matrix.one_apply,
    ite_and, Finset.sum_mul, mul_assoc]
  split_ifs <;> simp_all [mul_comm]

private lemma lift_orthogonality {I J E R : Type} [Fintype I] [Fintype J]
    [Fintype E] [Fintype R] [DecidableEq I] [DecidableEq J]
    [DecidableEq E] [DecidableEq R]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (V : Matrix (J × E) I ℂ)
    (hc : ∀ X ∈ T, ∀ Y : Matrix E E ℂ, Vᴴ * (X ⊗ₖ Y) * V ∈ S)
    (D : Matrix (I × R) (I × R) ℂ)
    (hD : ∀ X ∈ S, ∀ Y : Matrix R R ℂ, Matrix.trace (Dᴴ * (X ⊗ₖ Y)) = 0)
    (X : Matrix J J ℂ) (hX : X ∈ T) (Y : Matrix (E × R) (E × R) ℂ) :
    Matrix.trace (((liftEncoding (R := R) V) * D * (liftEncoding (R := R) V)ᴴ)ᴴ * (X ⊗ₖ Y)) = 0 := by
  rw [trace_pull]
  induction Y using Matrix.induction_on' with
  | h_zero => simp
  | h_add A B ha hb =>
    simp only [Matrix.kronecker_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.trace_add, ha, hb, add_zero]
  | h_std_basis a b z =>
    rw [lift_compress_single]
    exact hD _ (hc X hX _) _

private lemma reindex_trace {A B : Type} [Fintype A] [Fintype B]
    (e : B ≃ A) (D X : Matrix A A ℂ) :
    Matrix.trace ((D.submatrix e e)ᴴ * X.submatrix e e) = Matrix.trace (Dᴴ * X) := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact Equiv.sum_comp e (fun i => (Dᴴ * X) i i)

private lemma feasible_transfer {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (h : GraphHom S T) {m : ℕ}
    (hm : m ∈ {m | ∃ a r : ℕ, 0 < a ∧ 0 < r ∧
      ∃ rho : Matrix (Fin a) (Fin a) ℂ, rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
      ∃ W : Fin m → Matrix (I × Fin r) (Fin a) ℂ,
        (∀ j, (W j)ᴴ * W j = 1) ∧ ∀ j k, j ≠ k → ∀ X ∈ S,
          ∀ Y : Matrix (Fin r) (Fin r) ℂ,
            Matrix.trace ((W j * rho * (W k)ᴴ)ᴴ * (X ⊗ₖ Y)) = 0}) :
    m ∈ {m | ∃ a r : ℕ, 0 < a ∧ 0 < r ∧
      ∃ rho : Matrix (Fin a) (Fin a) ℂ, rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
      ∃ W : Fin m → Matrix (J × Fin r) (Fin a) ℂ,
        (∀ j, (W j)ᴴ * W j = 1) ∧ ∀ j k, j ≠ k → ∀ X ∈ T,
          ∀ Y : Matrix (Fin r) (Fin r) ℂ,
            Matrix.trace ((W j * rho * (W k)ᴴ)ᴴ * (X ⊗ₖ Y)) = 0} := by
  classical
  obtain ⟨e,he,V,hV,hc⟩ := h
  obtain ⟨a,r,ha,hr,rho,hpos,htr,W,hW,ho⟩ := hm
  let L := liftEncoding (R := Fin r) V
  let q : J × Fin (e*r) ≃ J × (Fin e × Fin r) :=
    Equiv.prodCongr (Equiv.refl J) finProdFinEquiv.symm
  let U (j : Fin m) := (L * W j).submatrix q id
  refine ⟨a,e*r,ha,Nat.mul_pos he hr,rho,hpos,htr,U,?_,?_⟩
  · intro j
    dsimp [U]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id, Matrix.conjTranspose_mul]
    have hl := lift_isometry (R := Fin r) V hV
    change Lᴴ * L = 1 at hl
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Lᴴ L, hl, Matrix.one_mul]
    exact hW j
  · intro j k hjk X hX Y
    let Z : Matrix (Fin e × Fin r) (Fin e × Fin r) ℂ :=
      Y.submatrix finProdFinEquiv finProdFinEquiv
    have ht := lift_orthogonality S T V hc (W j * rho * (W k)ᴴ)
      (ho j k hjk) X hX Z
    have hD : U j * rho * (U k)ᴴ =
        (L * (W j * rho * (W k)ᴴ) * Lᴴ).submatrix q q := by
      simp only [U,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_mul]
      change (L * W j).submatrix q (Equiv.refl (Fin a)) *
        rho.submatrix (Equiv.refl (Fin a)) (Equiv.refl (Fin a)) *
        ((W k)ᴴ * Lᴴ).submatrix (Equiv.refl (Fin a)) q = _
      rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
      simp only [Matrix.mul_assoc]
    have hK : X ⊗ₖ Y = (X ⊗ₖ Z).submatrix q q := by
      ext ⟨i,s⟩ ⟨l,t⟩
      change X i l * Y s t = X i l *
        Y (finProdFinEquiv (finProdFinEquiv.symm s))
          (finProdFinEquiv (finProdFinEquiv.symm t))
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [hD,hK,reindex_trace]
    exact ht


theorem solution {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (_hS : IsSystem S) (hT : IsSystem T) (h : GraphHom S T) :
    alphaEA S ≤ alphaEA T := by
  apply csSup_le'
  intro m hm
  apply le_csSup _ (feasible_transfer S T h hm)
  refine ⟨Fintype.card J ^ 2, ?_⟩
  rintro n ⟨a,r,ha,hr,rho,hpos,htr,W,hW,ho⟩
  exact assisted_message_dimension_bound T hT ha hr rho hpos htr W hW ho

#print axioms solution
