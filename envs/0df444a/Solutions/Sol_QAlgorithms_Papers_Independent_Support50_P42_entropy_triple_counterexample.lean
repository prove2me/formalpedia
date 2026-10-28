-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P42.entropy_triple_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:46:15.371987+00:00
-- url     : https://prove2.me/submissions/74859d5d-3c02-4b7a-b63a-03708e0c6cf7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

-- ===== ETC =====

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder MatrixOrder Kronecker

namespace X4ET

open Matrix QAlgorithms

/-! Generic: Hermitian `X` with `X * X = c • X`. -/

section gen
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spec_of {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {c : ℝ} (h : X * X = (c : ℂ) • X) :
    ∀ x ∈ spectrum ℝ X, x = 0 ∨ x = c := by
  have hsa : IsSelfAdjoint X := hX
  have e : cfc (fun x : ℝ => x * x) X = cfc (fun x : ℝ => c * x) X := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) X, cfc_id' ℝ X, cfc_const_mul_id c X, h]
    rw [Complex.coe_smul]
  intro x hx
  have := (eqOn_of_cfc_eq_cfc e : Set.EqOn _ _ _) hx
  simp only at this
  have : x * (x - c) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (by linarith)

lemma vn_scaled {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {c : ℝ} (h : X * X = (c : ℂ) • X) :
    vnEntropy X = -(Real.logb 2 c * X.trace.re) := by
  unfold vnEntropy
  have hsa : IsSelfAdjoint X := hX
  rw [cfc_congr (g := fun x : ℝ => Real.logb 2 c * x)]
  · rw [cfc_const_mul_id _ X, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul]
  · intro x hx
    rcases spec_of hX h x hx with rfl | rfl
    · simp
    · ring

lemma psd_scaled {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {c : ℝ} (hc : 0 < c)
    (h : X * X = (c : ℂ) • X) : X.PosSemidef := by
  have e : X = ((c⁻¹ : ℝ) : ℂ) • (Xᴴ * X) := by
    rw [hX.eq, h, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one,
      one_smul]
  rw [e]
  exact (posSemidef_conjTranspose_mul_self X).smul (by exact_mod_cast (inv_pos.2 hc).le)

lemma tr_psd {P L : Matrix ι ι ℂ} (hP : P.PosSemidef) (hL : L.PosSemidef) :
    0 ≤ (P * L).trace.re := by
  have h0 : 0 ≤ L := by
    rw [Matrix.nonneg_iff_posSemidef]; exact hL
  have hs : IsSelfAdjoint (CFC.sqrt L) := (CFC.sqrt_nonneg L).isSelfAdjoint
  have hL' : L = (CFC.sqrt L)ᴴ * CFC.sqrt L := by
    rw [← Matrix.star_eq_conjTranspose, hs.star_eq, CFC.sqrt_mul_sqrt_self L h0]
  rw [hL']
  set B := CFC.sqrt L
  have : (P * (Bᴴ * B)).trace = (B * P * Bᴴ).trace := by
    rw [← mul_assoc, Matrix.trace_mul_comm, ← mul_assoc]
  rw [this]
  exact (Complex.nonneg_iff.1 (hP.mul_mul_conjTranspose_same B).trace_nonneg).1

end gen

open QAlgorithms.Papers.Independent.Support50.P42

abbrev O4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-! `twoPairs` algebra. -/

lemma tp_mul (A B C D : O4) : twoPairs A B * twoPairs C D = twoPairs (A * C) (B * D) := by
  ext x y
  simp only [twoPairs, mul_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma tp_conj (A B : O4) : (twoPairs A B)ᴴ = twoPairs Aᴴ Bᴴ := by
  ext x y; simp [twoPairs, conjTranspose_apply, mul_comm]

lemma tp_smul_left (c : ℂ) (A B : O4) : twoPairs (c • A) B = c • twoPairs A B := by
  ext x y; simp [twoPairs, mul_assoc]

lemma tp_smul_right (c : ℂ) (A B : O4) : twoPairs A (c • B) = c • twoPairs A B := by
  ext x y; simp [twoPairs]; ring

lemma tp_trace (A B : O4) : (twoPairs A B).trace = A.trace * B.trace := by
  simp only [Matrix.trace, diag, twoPairs, Fintype.sum_prod_type, Finset.sum_mul_sum]

lemma tp_left (A B : O4) : traceLeft (twoPairs A B) = (traceLeft A) ⊗ₖ (traceLeft B) := by
  ext x y
  simp only [traceLeft, twoPairs, of_apply, kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma tp_right (A B : O4) : traceRight (twoPairs A B) = (traceRight A) ⊗ₖ (traceRight B) := by
  ext x y
  simp only [traceRight, twoPairs, of_apply, kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-! Concrete states. -/

def tR (x : Fin 2 × Fin 2) : ℝ := if x = (0, 1) then 1 else if x = (1, 0) then -1 else 0

def t (x : Fin 2 × Fin 2) : ℂ := ((tR x : ℝ) : ℂ)

lemma sv_apply (x : Fin 2 × Fin 2) :
    QAlgorithms.Papers.Independent.Dependency50.P42.singletVector x =
      ((Real.sqrt 2 / 2 * tR x : ℝ) : ℂ) := by
  obtain ⟨x1, x2⟩ := x
  fin_cases x1 <;> fin_cases x2 <;>
    simp [QAlgorithms.Papers.Independent.Dependency50.P42.singletVector, tR]

lemma s_apply (x y : Fin 2 × Fin 2) :
    QAlgorithms.Papers.Independent.Dependency50.P42.singletState x y = (1 / 2 : ℂ) * t x * t y := by
  simp only [QAlgorithms.Papers.Independent.Dependency50.P42.singletState, pureDensity, of_apply,
    sv_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, t]
  have : Real.sqrt 2 / 2 * tR x * (Real.sqrt 2 / 2 * tR y) = 1 / 2 * tR x * tR y := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    linear_combination (tR x * tR y / 4) * this
  rw [this]; push_cast; ring

lemma cp_apply (x y : Fin 2 × Fin 2) :
    classicalPair x y = if x = y ∧ x.1 = x.2 then (1 / 2 : ℂ) else 0 := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
    simp [classicalPair, pureDensity, ket, EuclideanSpace.single_apply]

end X4ET

-- ===== ETC2 =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open Information100.P21 (Op Vec FiniteLOCC)

namespace X4ET2

open Matrix X4ET

abbrev S : Op (Fin 2 × Fin 2) := Dependency50.P42.singletState
abbrev Q : Op (Fin 2 × Fin 2) := (1/4 : ℂ) • 1
abbrev H2 : Op (Fin 2) := (1/2 : ℂ) • 1

/-! Generic scaled-idempotent facts for kronecker / twoPairs. -/

lemma kron_sq {α β : Type*} [Fintype α] [Fintype β] {A : Op α} {B : Op β} {a b : ℂ}
    (hA : A * A = a • A) (hB : B * B = b • B) : (A ⊗ₖ B) * (A ⊗ₖ B) = (a * b) • (A ⊗ₖ B) := by
  rw [← Matrix.mul_kronecker_mul, hA, hB, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]

lemma kron_herm {α β : Type*} {A : Op α} {B : Op β} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ⊗ₖ B).IsHermitian := by
  unfold IsHermitian; rw [Matrix.conjTranspose_kronecker, hA.eq, hB.eq]

lemma H2_sq : H2 * H2 = (1/2 : ℂ) • H2 := by
  simp only [H2, smul_mul_smul_comm, mul_one, smul_smul]

lemma H2_herm : H2.IsHermitian := by
  unfold IsHermitian; simp [H2, conjTranspose_smul]

lemma H2_tr : H2.trace = 1 / 2 * 2 := by simp [H2]

lemma lb4 : Real.logb 2 (1/4) = -2 := by
  rw [one_div, Real.logb_inv, show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

lemma H4 : (H2 ⊗ₖ H2) * (H2 ⊗ₖ H2) = ((1/4 : ℝ) : ℂ) • (H2 ⊗ₖ H2) := by
  rw [kron_sq H2_sq H2_sq]; norm_num

lemma H4_tr : (H2 ⊗ₖ H2).trace = 1 := by
  rw [Matrix.trace_kronecker, H2_tr]; norm_num

lemma vn_H4 : vnEntropy (H2 ⊗ₖ H2) = 2 := by
  rw [vn_scaled (kron_herm H2_herm H2_herm) H4, H4_tr]
  rw [lb4]; simp

/-! Concrete states. -/

lemma S_herm : S.IsHermitian := by
  ext x y; simp [S, s_apply, t]; ring

lemma S_sq : S * S = (1 : ℂ) • S := by
  ext x y
  simp only [S, mul_apply, s_apply, Fintype.sum_prod_type, Fin.sum_univ_two, one_smul, t, tR]
  simp; ring

lemma S_tr : S.trace = 1 := by
  simp [S, Matrix.trace, s_apply, Fintype.sum_prod_type, Fin.sum_univ_two, t, tR]; norm_num

lemma S_left : traceLeft S = H2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [S, traceLeft, s_apply, Fin.sum_univ_two, t, tR, H2, one_apply] <;> norm_num

lemma S_right : traceRight S = H2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [S, traceRight, s_apply, Fin.sum_univ_two, t, tR, H2, one_apply] <;> norm_num

lemma cp_herm : classicalPair.IsHermitian := by
  ext x y; simp only [conjTranspose_apply, cp_apply]
  by_cases h : y = x
  · subst h; split_ifs <;> simp
  · rw [if_neg (by tauto), if_neg (by intro h'; exact h h'.1.symm)]; simp

lemma cp_sq : classicalPair * classicalPair = (1/2 : ℂ) • classicalPair := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [mul_apply, cp_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;> norm_num

lemma cp_tr : classicalPair.trace = 1 := by
  simp only [Matrix.trace, diag, cp_apply, Fintype.sum_prod_type, Fin.sum_univ_two]; norm_num

lemma cp_left : traceLeft classicalPair = H2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [traceLeft, cp_apply, Fin.sum_univ_two, H2, one_apply] <;> norm_num

lemma cp_right : traceRight classicalPair = H2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [traceRight, cp_apply, Fin.sum_univ_two, H2, one_apply] <;> norm_num

lemma Q_herm : Q.IsHermitian := by
  unfold IsHermitian; simp [Q, conjTranspose_smul]

lemma Q_sq : Q * Q = (1/4 : ℂ) • Q := by
  simp only [Q, smul_mul_smul_comm, mul_one, smul_smul]

lemma Q_tr : Q.trace = 1 := by
  simp [Q]

lemma Q_left : traceLeft Q = H2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Q, traceLeft, Fin.sum_univ_two, H2, one_apply] <;> norm_num

lemma Q_right : traceRight Q = H2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Q, traceRight, Fin.sum_univ_two, H2, one_apply] <;> norm_num

/-! The two four-spin states. -/

lemma tp_herm {A B : Op (Fin 2 × Fin 2)} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (twoPairs A B).IsHermitian := by
  unfold IsHermitian; rw [tp_conj, hA.eq, hB.eq]

lemma tp_sq {A B : Op (Fin 2 × Fin 2)} {a b : ℂ} (hA : A * A = a • A) (hB : B * B = b • B) :
    twoPairs A B * twoPairs A B = (a * b) • twoPairs A B := by
  rw [tp_mul, hA, hB, tp_smul_left, tp_smul_right, smul_smul, mul_comm]

lemma tp_density {A B : Op (Fin 2 × Fin 2)} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : twoPairs A B * twoPairs A B = ((1/4 : ℝ) : ℂ) • twoPairs A B)
    (htr : (twoPairs A B).trace = 1) :
    IsDensityMatrix (twoPairs A B) ∧ vnEntropy (twoPairs A B) = 2 := by
  refine ⟨⟨psd_scaled (tp_herm hA hB) (by norm_num) h, htr⟩, ?_⟩
  rw [vn_scaled (tp_herm hA hB) h, htr]
  rw [lb4]; simp

lemma rho_facts : IsDensityMatrix (twoPairs classicalPair classicalPair) ∧
    vnEntropy (twoPairs classicalPair classicalPair) = 2 := by
  refine tp_density cp_herm cp_herm ?_ ?_
  · rw [tp_sq cp_sq cp_sq]; norm_num
  · rw [tp_trace, cp_tr, one_mul]

lemma sigma_facts : IsDensityMatrix (twoPairs S Q) ∧ vnEntropy (twoPairs S Q) = 2 := by
  refine tp_density S_herm Q_herm ?_ ?_
  · rw [tp_sq S_sq Q_sq]; norm_num
  · rw [tp_trace, S_tr, Q_tr, one_mul]

/-! Separability. -/

def D (p : Fin 2 × Fin 2) : Op (Fin 2 × Fin 2) := diagonal fun x => if x = p then 1 else 0

lemma D_density (p : Fin 2 × Fin 2) : IsDensityMatrix (D p) := by
  refine ⟨?_, ?_⟩
  · rw [D, posSemidef_diagonal_iff]; intro x; split_ifs <;> simp
  · simp [D, Matrix.trace_diagonal]

lemma rho_sep : Entanglement.IsSeparablePositive (twoPairs classicalPair classicalPair) := by
  let e : Fin 4 → Fin 2 × Fin 2 := fun j =>
    if j = 0 then (0, 0) else if j = 1 then (0, 1) else if j = 2 then (1, 0) else (1, 1)
  refine ⟨4, fun _ => 1/4, fun j => D (e j), fun j => D (e j), fun _ => by norm_num,
    fun j => ⟨D_density _, D_density _⟩, ?_⟩
  ext ⟨⟨a1, a2⟩, b1, b2⟩ ⟨⟨c1, c2⟩, d1, d2⟩
  simp only [twoPairs, cp_apply, Matrix.sum_apply, Fin.sum_univ_four, Matrix.smul_apply,
    kroneckerMap_apply, D, diagonal_apply, smul_eq_mul, e]
  simp only [show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide, if_true, if_false]
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    fin_cases c1 <;> fin_cases c2 <;> fin_cases d1 <;> fin_cases d2 <;> norm_num

def G : Op ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) →ₗ[ℂ] ℂ where
  toFun X := ∑ i : Fin 2, ∑ j : Fin 2, ∑ a : Fin 2, ∑ b : Fin 2, X ((i, a), (j, b)) ((j, a), (i, b))
  map_add' X Y := by simp [Finset.sum_add_distrib]
  map_smul' c X := by simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

lemma G_kron {A B : Op (Fin 2 × Fin 2)} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (G (A ⊗ₖ B)).re := by
  have e : G (A ⊗ₖ B) = ∑ a : Fin 2, ∑ b : Fin 2,
      (A.submatrix (fun i => (i, a)) (fun i => (i, a)) *
        B.submatrix (fun i => (i, b)) (fun i => (i, b))).trace := by
    simp only [G, LinearMap.coe_mk, AddHom.coe_mk, kroneckerMap_apply, Matrix.trace, diag,
      mul_apply, submatrix_apply, Fin.sum_univ_two]
    ring
  rw [e, Complex.re_sum]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun b _ => tr_psd (hA.submatrix _) (hB.submatrix _)

lemma G_sigma : G (twoPairs S Q) = -1 := by
  simp [G, twoPairs, s_apply, t, tR, Q, Fin.sum_univ_two, one_apply]
  norm_num

lemma sigma_nsep : ¬ Entanglement.IsSeparablePositive (twoPairs S Q) := by
  rintro ⟨q, w, A, B, hw, hd, heq⟩
  have h : 0 ≤ (G (twoPairs S Q)).re := by
    rw [heq, map_sum, Complex.re_sum]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_nonneg (hw j) (G_kron (hd j).1.1 (hd j).2.1)
  rw [G_sigma] at h
  norm_num at h

lemma discard_sigma : discardSecond (twoPairs S Q) = S := by
  ext x y
  simp [discardSecond, twoPairs, Q, Fin.sum_univ_two, one_apply]
  ring

lemma vn_marg {A B : Op (Fin 2 × Fin 2)} (hA : traceLeft A = H2) (hB : traceLeft B = H2)
    (hA' : traceRight A = H2) (hB' : traceRight B = H2) :
    vnEntropy (traceLeft (twoPairs A B)) = 2 ∧ vnEntropy (traceRight (twoPairs A B)) = 2 := by
  rw [tp_left, tp_right, hA, hB, hA', hB']
  exact ⟨vn_H4, vn_H4⟩

end X4ET2

end QAlgorithms.Papers.Independent.Support50.P42

-- ===== ETCSol =====
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF p.16: two four-spin mixed states with all three entropies equal to two.
The second uncorrelated pair is maximally mixed. The first state is separable;
the second is entangled and yields a singlet upon local disposal. -/
theorem _root_.solution :
    let rho := twoPairs classicalPair classicalPair
    let sigma := twoPairs Dependency50.P42.singletState ((1/4 : ℂ) • 1)
    IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
    vnEntropy rho=2 ∧ vnEntropy (traceLeft rho)=2 ∧ vnEntropy (traceRight rho)=2 ∧
    vnEntropy sigma=2 ∧ vnEntropy (traceLeft sigma)=2 ∧ vnEntropy (traceRight sigma)=2 ∧
    Entanglement.IsSeparablePositive rho ∧ ¬Entanglement.IsSeparablePositive sigma ∧
    discardSecond sigma=Dependency50.P42.singletState := by
  intro rho sigma
  obtain ⟨h1, h2⟩ := X4ET2.rho_facts
  obtain ⟨h3, h4⟩ := X4ET2.sigma_facts
  obtain ⟨h5, h6⟩ := X4ET2.vn_marg X4ET2.cp_left X4ET2.cp_left X4ET2.cp_right X4ET2.cp_right
  obtain ⟨h7, h8⟩ := X4ET2.vn_marg X4ET2.S_left X4ET2.Q_left X4ET2.S_right X4ET2.Q_right
  exact ⟨h1, h3, h2, h5, h6, h4, h7, h8, X4ET2.rho_sep, X4ET2.sigma_nsep, X4ET2.discard_sigma⟩

end QAlgorithms.Papers.Independent.Support50.P42

end
