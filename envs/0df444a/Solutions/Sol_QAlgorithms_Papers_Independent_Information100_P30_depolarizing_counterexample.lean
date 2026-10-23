-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P30.depolarizing_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:00:34.247363+00:00
-- url     : https://prove2.me/submissions/4536f308-dff8-4240-a81b-b5a1c04ce450

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem x8_D_apply (q : ℝ) (X : Matrix Bool Bool ℂ) (i j : Bool) :
    depolarizing q X i j = (q : ℂ) * X i j +
      (((1 - q) / 2 : ℝ) : ℂ) * (X false false + X true true) * (if i = j then 1 else 0) := by
  simp [depolarizing, Matrix.trace, Matrix.one_apply, add_comm]

def x8σx : Matrix Bool Bool ℂ := Matrix.of fun i j => if i = j then 0 else 1
def x8σy : Matrix Bool Bool ℂ := Matrix.of fun i j => if i = j then 0 else (if i then Complex.I else -Complex.I)
def x8σz : Matrix Bool Bool ℂ := Matrix.of fun i j => if i = j then (if i then -1 else 1) else 0

def x8K (a b : ℂ) : Fin 4 → Matrix Bool Bool ℂ :=
  ![a • (1 : Matrix Bool Bool ℂ), b • x8σx, b • x8σy, b • x8σz]

theorem x8_K_family (a b : ℂ) (h : conj a * a + 3 * (conj b * b) = 1) : IsKrausFamily (x8K a b) := by
  unfold IsKrausFamily
  ext i j
  simp only [x8K, Fin.sum_univ_four, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_bool,
    Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, x8σx, x8σy, x8σz, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul, star_mul']
  cases i <;> cases j <;> simp <;> first | linear_combination h - (conj b * b) * Complex.I_sq | linear_combination h | ring1

theorem x8_K_apply (a b : ℂ) (X : Matrix Bool Bool ℂ) (i j : Bool) :
    krausApply (x8K a b) X i j = (conj a * a - conj b * b) * X i j +
      2 * (conj b * b) * (X false false + X true true) * (if i = j then 1 else 0) := by
  simp only [krausApply, x8K, Fin.sum_univ_four, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_bool,
    Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, x8σx, x8σy, x8σz, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul, star_mul']
  cases i <;> cases j <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem x8_D_channel (q : ℝ) (h0 : -1/3 ≤ q) (h1 : q ≤ 1) : IsChannel (depolarizing q) := by
  set a : ℂ := ((Real.sqrt ((1 + 3 * q) / 4) : ℝ) : ℂ) with ha'
  set b : ℂ := ((Real.sqrt ((1 - q) / 4) : ℝ) : ℂ) with hb'
  have ha : conj a * a = (((1 + 3 * q) / 4 : ℝ) : ℂ) := by
    rw [ha', Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hb : conj b * b = (((1 - q) / 4 : ℝ) : ℂ) := by
    rw [hb', Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  refine ⟨4, x8K a b, x8_K_family a b ?_, fun X => ?_⟩
  · rw [ha, hb]; push_cast; ring
  · ext i j
    rw [x8_K_apply, x8_D_apply, ha, hb]
    push_cast; ring

theorem x8_D_comp (a b : ℝ) : (depolarizing a).comp (depolarizing b) = depolarizing (a * b) := by
  apply LinearMap.ext; intro X
  ext i j
  simp only [LinearMap.comp_apply, x8_D_apply]
  cases i <;> cases j <;> simp <;> push_cast <;> ring

theorem x8_trace_real {I : Type*} [Fintype I] {M : Matrix I I ℂ} (hM : M.PosSemidef) :
    M.trace = ((M.trace.re : ℝ) : ℂ) := by
  have h := (Complex.nonneg_iff.1 hM.trace_nonneg).2
  apply Complex.ext <;> simp [← h]

theorem x8_normalize {I : Type*} [Fintype I] [Nonempty I] {M : Matrix I I ℂ} (hM : M.PosSemidef) :
    ∃ A : Matrix I I ℂ, IsDensityMatrix A ∧ M = ((M.trace.re : ℝ) : ℂ) • A := by
  classical
  by_cases h0 : M.trace = 0
  · refine ⟨Matrix.diagonal (Pi.single (Classical.arbitrary I) 1), ⟨?_, ?_⟩, ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]; intro i
      by_cases hi : i = Classical.arbitrary I
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    · simp [Matrix.trace_diagonal]
    · rw [(hM.trace_eq_zero_iff).1 h0]; simp
  · set t := M.trace.re with ht
    have htr := x8_trace_real hM
    have htpos : t ≠ 0 := by intro h; apply h0; rw [htr, ← ht, h]; simp
    refine ⟨((t⁻¹ : ℝ) : ℂ) • M, ⟨hM.smul (Complex.zero_le_real.2 (inv_nonneg.2 ?_)), ?_⟩, ?_⟩
    · rw [ht]; exact (Complex.nonneg_iff.1 hM.trace_nonneg).1
    · rw [Matrix.trace_smul, htr, ← ht, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ htpos]
      simp
    · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ htpos]; simp

theorem x8_sep {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] (m : ℕ)
    (M : Fin m → Matrix I I ℂ) (N : Fin m → Matrix J J ℂ)
    (hM : ∀ n, (M n).PosSemidef) (hN : ∀ n, (N n).PosSemidef) :
    ∃ w : Fin m → ℝ, ∃ A : Fin m → Matrix I I ℂ, ∃ B : Fin m → Matrix J J ℂ,
      (∀ j, 0 ≤ w j) ∧ (∀ j, IsDensityMatrix (A j) ∧ IsDensityMatrix (B j)) ∧
      (∑ n, Matrix.kronecker (M n) (N n)) = ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j) ∧
      ((∑ j, w j : ℝ) : ℂ) = (∑ n, Matrix.kronecker (M n) (N n)).trace := by
  choose A hA hMA using fun n => x8_normalize (hM n)
  choose B hB hNB using fun n => x8_normalize (hN n)
  refine ⟨fun n => (M n).trace.re * (N n).trace.re, A, B, fun n => mul_nonneg
    (Complex.nonneg_iff.1 (hM n).trace_nonneg).1 (Complex.nonneg_iff.1 (hN n).trace_nonneg).1,
    fun n => ⟨hA n, hB n⟩, ?_, ?_⟩
  · refine Finset.sum_congr rfl fun n _ => ?_
    conv_lhs => rw [hMA n, hNB n]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply]; ring
  · rw [Matrix.trace_sum]; push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold Matrix.kronecker
    rw [Matrix.trace_kronecker, ← x8_trace_real (hM n), ← x8_trace_real (hN n)]

def x8v (x y : ℂ) : Bool → ℂ := fun b => if b then y else x

@[simp] theorem x8v_false (x y : ℂ) : x8v x y false = x := rfl
@[simp] theorem x8v_true (x y : ℂ) : x8v x y true = y := rfl

theorem x8_cnonneg (r : ℝ) (h : 0 ≤ r) (c : ℂ) (hc : c = (r : ℂ)) : 0 ≤ c := by
  rw [hc]; exact Complex.zero_le_real.2 h

def x8quad (φ : Bool → ℂ) (Y : Matrix Bool Bool ℂ) : ℂ :=
  ∑ i, ∑ i', conj (φ i) * Y i i' * φ i'

/-- contraction of the second factor against `φ` -/
def x8Mφ {R : Type*} (φ : Bool → ℂ) (X : Matrix (R × Bool) (R × Bool) ℂ) : Matrix R R ℂ :=
  Matrix.of fun a a' => ∑ i, ∑ i', conj (φ i) * X (a, i) (a', i') * φ i'

theorem x8Mφ_psd {R : Type*} [Fintype R] [DecidableEq R] (φ : Bool → ℂ)
    {X : Matrix (R × Bool) (R × Bool) ℂ} (hX : X.PosSemidef) : (x8Mφ φ X).PosSemidef := by
  let V : Matrix (R × Bool) R ℂ := Matrix.of fun p a => if p.1 = a then φ p.2 else 0
  have h : x8Mφ φ X = Vᴴ * X * V := by
    ext a a'
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply, x8Mφ,
      Fintype.sum_prod_type]
    simp [Finset.sum_mul, ite_mul, apply_ite (star : ℂ → ℂ), Fintype.sum_bool]
    ring
  rw [h]; exact hX.conjTranspose_mul_mul_same V

theorem x8_idT_decomp {R : Type*} [Fintype R] {m : ℕ} (Φ : Matrix Bool Bool ℂ → Matrix Bool Bool ℂ)
    (φ : Fin m → Bool → ℂ) (N : Fin m → Matrix Bool Bool ℂ)
    (hΦ : ∀ Y, Φ Y = ∑ n, x8quad (φ n) Y • N n) (X : Matrix (R × Bool) (R × Bool) ℂ) :
    idTensorSuperop Φ X = ∑ n, Matrix.kronecker (x8Mφ (φ n) X) (N n) := by
  ext p q
  simp only [idTensorSuperop, Matrix.of_apply, hΦ, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.kronecker, Matrix.kroneckerMap_apply, x8quad, x8Mφ]

def x8φ : Fin 8 → Bool → ℂ :=
  ![x8v 1 1, x8v 1 (-1), x8v 1 Complex.I, x8v 1 (-Complex.I), x8v 1 0, x8v 0 1, x8v 1 0, x8v 0 1]

def x8N : Fin 8 → Matrix Bool Bool ℂ := fun n =>
  if n.val < 4 then (1 / 16 : ℂ) • Matrix.vecMulVec (x8φ n) (star (x8φ n))
  else if n.val < 6 then (1 / 4 : ℂ) • Matrix.vecMulVec (x8φ n) (star (x8φ n))
  else (1 / 8 : ℂ) • 1

theorem x8N_psd (n : Fin 8) : (x8N n).PosSemidef := by
  unfold x8N
  split_ifs
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (x8_cnonneg (1/16) (by norm_num) _ (by push_cast; ring))
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (x8_cnonneg (1/4) (by norm_num) _ (by push_cast; ring))
  · exact Matrix.PosSemidef.one.smul (x8_cnonneg (1/8) (by norm_num) _ (by push_cast; ring))

theorem x8_D14 (Y : Matrix Bool Bool ℂ) :
    depolarizing (1/4) Y = ∑ n, x8quad (x8φ n) Y • x8N n := by
  ext i j
  rw [x8_D_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Fin.sum_univ_eight, x8N, x8φ, x8quad,
    Fintype.sum_bool, Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul, Pi.star_apply]
  cases i <;> cases j <;> simp [Matrix.vecMulVec_apply] <;> ring_nf <;> simp [Complex.I_sq, Complex.conj_I] <;> ring_nf

theorem x8_tr_idT {R : Type*} [Fintype R] (q : ℝ) (X : Matrix (R × Bool) (R × Bool) ℂ) :
    (idTensorSuperop (depolarizing q) X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, idTensorSuperop, Matrix.of_apply, x8_D_apply,
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, if_false, Bool.false_eq_true, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  push_cast; ring

theorem x8_EB14 : Entanglement.IsEntanglementBreaking (depolarizing (1/4)) := by
  intro a ha X hX
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  rw [x8_idT_decomp _ x8φ x8N x8_D14 X]
  obtain ⟨w, A, B, hw, hd, heq, htr⟩ := x8_sep 8 (fun n => x8Mφ (x8φ n) X) x8N
    (fun n => x8Mφ_psd _ hX.1) x8N_psd
  refine ⟨8, w, A, B, hw, ?_, hd, heq⟩
  have h1 : (∑ n, Matrix.kronecker (x8Mφ (x8φ n) X) (x8N n)).trace = 1 := by
    rw [← x8_idT_decomp _ x8φ x8N x8_D14 X, x8_tr_idT, hX.2]
  rw [h1] at htr
  exact_mod_cast htr

lemma x8_ppt {I J : Type} [Fintype I] [Fintype J] (X : Matrix (I × J) (I × J) ℂ)
    (hX : Entanglement.IsSeparablePositive X) (v : I → J → ℂ) :
    0 ≤ (∑ i, ∑ j, ∑ i', ∑ j', conj (v i j) * X (i, j') (i', j) * v i' j').re := by
  obtain ⟨q, w, A, B, hw, hd, rfl⟩ := hX
  have key : ∀ t, 0 ≤ (∑ i, ∑ j, ∑ i', ∑ j',
      conj (v i j) * (A t i i' * B t j' j) * v i' j').re := by
    intro t
    have hP : (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (A t) (B t)ᵀ).PosSemidef :=
      (hd t).1.1.kronecker (hd t).2.1.transpose
    have h := hP.dotProduct_mulVec_nonneg (fun p => v p.1 p.2)
    have h2 : star (fun p : I × J => v p.1 p.2) ⬝ᵥ
        (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (A t) (B t)ᵀ) *ᵥ (fun p => v p.1 p.2) =
        ∑ i, ∑ j, ∑ i', ∑ j', conj (v i j) * (A t i i' * B t j' j) * v i' j' := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum,
        Matrix.kroneckerMap_apply, Matrix.transpose_apply, Pi.star_apply, RCLike.star_def]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
      ring
    rw [h2] at h
    exact (Complex.nonneg_iff.1 h).1
  have hsum : (∑ i, ∑ j, ∑ i', ∑ j', conj (v i j) *
      (∑ t, (w t : ℂ) • Matrix.kronecker (A t) (B t) : Matrix (I × J) (I × J) ℂ) (i, j') (i', j) * v i' j') =
      ∑ t, (w t : ℂ) * ∑ i, ∑ j, ∑ i', ∑ j', conj (v i j) * (A t i i' * B t j' j) * v i' j' := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [hsum, Complex.re_sum]
  refine Finset.sum_nonneg fun t _ => ?_
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (hw t) (key t)

def x8bv : Fin 2 × Bool → ℂ := fun p => if (p.1 = 0 ∧ p.2 = false) ∨ (p.1 = 1 ∧ p.2 = true) then 1 else 0

def x8bell : Matrix (Fin 2 × Bool) (Fin 2 × Bool) ℂ := (1 / 2 : ℂ) • Matrix.vecMulVec x8bv (star x8bv)

theorem x8bell_density : IsDensityMatrix x8bell := by
  refine ⟨(Matrix.posSemidef_vecMulVec_self_star _).smul (x8_cnonneg (1/2) (by norm_num) _ (by push_cast; ring)), ?_⟩
  simp [x8bell, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.vecMulVec_apply, x8bv]
  norm_num

theorem x8_notEB12 : ¬ Entanglement.IsEntanglementBreaking (depolarizing (1/2)) := by
  intro h
  obtain ⟨q, w, A, B, hw, -, hd, heq⟩ := h 2 (by norm_num) x8bell x8bell_density
  have hsep : Entanglement.IsSeparablePositive (idTensorSuperop (depolarizing (1/2)) x8bell) :=
    ⟨q, w, A, B, hw, hd, heq⟩
  have H := x8_ppt _ hsep ![x8v 0 1, x8v (-1) 0]
  have hval : (∑ i, ∑ j, ∑ i', ∑ j', conj ((![x8v 0 1, x8v (-1) 0] : Fin 2 → Bool → ℂ) i j) *
      idTensorSuperop (depolarizing (1/2)) x8bell (i, j') (i', j) *
      (![x8v 0 1, x8v (-1) 0] : Fin 2 → Bool → ℂ) i' j') = -(1/4 : ℂ) := by
    simp only [idTensorSuperop, Matrix.of_apply, x8_D_apply]
    simp [Fin.sum_univ_two, Fintype.sum_bool, x8bell, Matrix.vecMulVec_apply, x8bv]
    norm_num
  rw [hval] at H
  norm_num at H

/-- contraction of the first factor against `φ` -/
def x8Lφ (φ : Bool → ℂ) (X : Matrix (Bool × Bool) (Bool × Bool) ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun j b => ∑ i, ∑ a, conj (φ i) * X (i, j) (a, b) * φ a

theorem x8Lφ_psd (φ : Bool → ℂ) {X : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hX : X.PosSemidef) :
    (x8Lφ φ X).PosSemidef := by
  let V : Matrix (Bool × Bool) Bool ℂ := Matrix.of fun p b => if p.2 = b then φ p.1 else 0
  have h : x8Lφ φ X = Vᴴ * X * V := by
    ext a a'
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply, x8Lφ,
      Fintype.sum_prod_type]
    simp [ite_mul, apply_ite (star : ℂ → ℂ), Fintype.sum_bool]
    ring
  rw [h]; exact hX.conjTranspose_mul_mul_same V

theorem x8_sepPos {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] (m : ℕ)
    (M : Fin m → Matrix I I ℂ) (N : Fin m → Matrix J J ℂ)
    (hM : ∀ n, (M n).PosSemidef) (hN : ∀ n, (N n).PosSemidef) :
    Entanglement.IsSeparablePositive (∑ n, Matrix.kronecker (M n) (N n)) := by
  obtain ⟨w, A, B, hw, hd, heq, -⟩ := x8_sep m M N hM hN
  exact ⟨m, w, A, B, hw, hd, heq⟩

theorem x8_sepPos_add {I J : Type*} [Fintype I] [Fintype J] {X Y : Matrix (I × J) (I × J) ℂ}
    (hX : Entanglement.IsSeparablePositive X) (hY : Entanglement.IsSeparablePositive Y) :
    Entanglement.IsSeparablePositive (X + Y) := by
  obtain ⟨q, w, A, B, hw, hd, rfl⟩ := hX
  obtain ⟨q', w', A', B', hw', hd', rfl⟩ := hY
  refine ⟨q + q', Fin.append w w', Fin.append A A', Fin.append B B', ?_, ?_, ?_⟩
  · intro t; refine Fin.addCases (fun i => ?_) (fun i => ?_) t <;> simp [hw, hw']
  · intro t; refine Fin.addCases (fun i => ?_) (fun i => ?_) t <;> simp [hd, hd']
  · rw [Fin.sum_univ_add]; simp

def x8N1 : Fin 6 → Matrix Bool Bool ℂ := fun n =>
  if n.val < 4 then (1 / 32 : ℂ) • Matrix.vecMulVec (x8φ n.castSucc.castSucc) (star (x8φ n.castSucc.castSucc))
  else (1 / 8 : ℂ) • Matrix.vecMulVec (x8φ n.castSucc.castSucc) (star (x8φ n.castSucc.castSucc))

theorem x8N1_psd (n : Fin 6) : (x8N1 n).PosSemidef := by
  unfold x8N1
  split_ifs
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (x8_cnonneg (1/32) (by norm_num) _ (by push_cast; ring))
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (x8_cnonneg (1/8) (by norm_num) _ (by push_cast; ring))

theorem x8_tm_apply (F G : MatrixMap Bool Bool) (X : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (p q : Bool × Bool) :
    tensorMap F G X p q = ∑ i, ∑ j, ∑ a, ∑ b,
      X (i, j) (a, b) * (F (Matrix.single i a 1) p.1 q.1 * G (Matrix.single j b 1) p.2 q.2) := by
  unfold tensorMap
  simp only [Matrix.sum_apply]
  rfl

theorem x8_Dsingle (q : ℝ) (i a k k' : Bool) :
    depolarizing q (Matrix.single i a 1) k k' =
      (q : ℂ) * (if i = k ∧ a = k' then 1 else 0) +
      (((1 - q) / 2 : ℝ) : ℂ) * (if i = a then 1 else 0) * (if k = k' then 1 else 0) := by
  rw [x8_D_apply]
  cases i <;> cases a <;> cases k <;> cases k' <;> simp [Matrix.single_apply]

theorem x8_tensorMap_apply (a b : ℝ) (X : Matrix (Bool × Bool) (Bool × Bool) ℂ) (k l k' l' : Bool) :
    tensorMap (depolarizing a) (depolarizing b) X (k, l) (k', l') =
      (a : ℂ) * b * X (k, l) (k', l') +
      (a : ℂ) * (((1 - b) / 2 : ℝ) : ℂ) * (if l = l' then 1 else 0) * (X (k, false) (k', false) + X (k, true) (k', true)) +
      (((1 - a) / 2 : ℝ) : ℂ) * b * (if k = k' then 1 else 0) * (X (false, l) (false, l') + X (true, l) (true, l')) +
      (((1 - a) / 2 : ℝ) : ℂ) * (((1 - b) / 2 : ℝ) : ℂ) * (if k = k' then 1 else 0) * (if l = l' then 1 else 0) *
        (X (false, false) (false, false) + X (false, true) (false, true) +
          X (true, false) (true, false) + X (true, true) (true, true)) := by
  rw [x8_tm_apply]
  simp only [x8_Dsingle, Fintype.sum_bool]
  cases k <;> cases l <;> cases k' <;> cases l' <;> simp <;> ring

theorem x8_N1_id (Y : Matrix Bool Bool ℂ) (k k' : Bool) :
    ∑ n, x8N1 n k k' * x8quad (x8φ n.castSucc.castSucc) Y =
      (1 / 8 : ℂ) * Y k k' + (1 / 8 : ℂ) * (Y false false + Y true true) * (if k = k' then 1 else 0) := by
  simp only [Fin.sum_univ_six, x8N1, x8φ, x8quad, Fintype.sum_bool, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Pi.star_apply]
  cases k <;> cases k' <;> simp [Matrix.vecMulVec_apply] <;> ring_nf <;> simp [Complex.I_sq, Complex.conj_I] <;> ring_nf

theorem x8_N1_id' (Y : Matrix Bool Bool ℂ) (k k' : Bool) :
    ∑ n, x8quad (x8φ n.castSucc.castSucc) Y * x8N1 n k k' =
      (1 / 8 : ℂ) * Y k k' + (1 / 8 : ℂ) * (Y false false + Y true true) * (if k = k' then 1 else 0) := by
  rw [← x8_N1_id]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem x8_EA_decomp (X : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    tensorMap (depolarizing (1/2)) (depolarizing (1/2)) X =
      (∑ n, Matrix.kronecker (x8N1 n) (x8Lφ (x8φ n.castSucc.castSucc) X)) +
      (∑ n, Matrix.kronecker (x8Mφ (x8φ n.castSucc.castSucc) X) (x8N1 n)) +
      Matrix.kronecker ((1 / 16 : ℂ) • X.trace • (1 : Matrix Bool Bool ℂ)) (1 : Matrix Bool Bool ℂ) := by
  ext ⟨k, l⟩ ⟨k', l'⟩
  rw [x8_tensorMap_apply]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  have h1 : ∀ n : Fin 6, x8Lφ (x8φ n.castSucc.castSucc) X l l' =
      x8quad (x8φ n.castSucc.castSucc) (Matrix.of fun i a => X (i, l) (a, l')) := fun _ => rfl
  have h2 : ∀ n : Fin 6, x8Mφ (x8φ n.castSucc.castSucc) X k k' =
      x8quad (x8φ n.castSucc.castSucc) (Matrix.of fun i a => X (k, i) (k', a)) := fun _ => rfl
  simp only [h1, h2, x8_N1_id, x8_N1_id', Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fintype.sum_bool]
  push_cast
  split_ifs <;> ring

theorem x8_EA : IsParallelEA (depolarizing (1/2)) (depolarizing (1/2)) := by
  intro X hX
  rw [x8_EA_decomp]
  refine x8_sepPos_add (x8_sepPos_add (x8_sepPos 6 _ _ x8N1_psd (fun n => x8Lφ_psd _ hX))
    (x8_sepPos 6 _ _ (fun n => x8Mφ_psd _ hX) x8N1_psd)) ?_
  have h := x8_sepPos 1 (fun _ => (1 / 16 : ℂ) • X.trace • (1 : Matrix Bool Bool ℂ))
    (fun _ => (1 : Matrix Bool Bool ℂ)) (fun _ => ?_) (fun _ => Matrix.PosSemidef.one)
  · simpa using h
  · rw [smul_smul]
    refine Matrix.PosSemidef.one.smul (x8_cnonneg ((1/16) * X.trace.re)
      (mul_nonneg (by norm_num) (Complex.nonneg_iff.1 hX.trace_nonneg).1) _ ?_)
    rw [x8_trace_real hX]; simp

theorem x8_main :
    IsQubitChannel (depolarizing (1/2)) ∧ IsQubitChannel (depolarizing (1/4)) ∧
    IsParallelEA (depolarizing (1/2)) (depolarizing (1/2)) ∧
    ¬ Entanglement.IsEntanglementBreaking (depolarizing (1/2)) ∧
    (depolarizing (1/2)).comp (depolarizing (1/2)) = depolarizing (1/4) ∧
    Entanglement.IsEntanglementBreaking (depolarizing (1/4)) := by
  refine ⟨x8_D_channel _ (by norm_num) (by norm_num), x8_D_channel _ (by norm_num) (by norm_num),
    x8_EA, x8_notEB12, ?_, x8_EB14⟩
  rw [x8_D_comp]; norm_num

end QAlgorithms.Papers.Independent.Information100.P30

open QAlgorithms.Papers.Independent.Information100.P30 in
theorem solution :
    IsQubitChannel (depolarizing (1/2)) ∧ IsQubitChannel (depolarizing (1/4)) ∧
    IsParallelEA (depolarizing (1/2)) (depolarizing (1/2)) ∧
    ¬ QAlgorithms.Entanglement.IsEntanglementBreaking (depolarizing (1/2)) ∧
    (depolarizing (1/2)).comp (depolarizing (1/2)) = depolarizing (1/4) ∧
    QAlgorithms.Entanglement.IsEntanglementBreaking (depolarizing (1/4)) :=
  QAlgorithms.Papers.Independent.Information100.P30.x8_main
