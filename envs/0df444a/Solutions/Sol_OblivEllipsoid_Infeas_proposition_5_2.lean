-- Prove2me | solution 1 for OblivEllipsoid.Infeas.proposition_5_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:58:37.036197+00:00
-- url     : https://prove2.me/submissions/de0c7a53-e307-464b-b027-82b653dac041

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model
import Theorems.Thm_OblivEllipsoid_Infeas_proposition_5_1
import Theorems.Thm_OblivEllipsoid_Infeas_proposition_4_1_b

open Matrix

namespace OblivEllipsoid.Infeas
namespace OEAProp52

variable {n m : ℕ}

lemma AT_mulVec_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) (k : Fin m) :
    (Aᵀ *ᵥ x) k = col A k ⬝ᵥ x := by
  simp [Matrix.mulVec, dotProduct, col, Matrix.transpose_apply]

lemma quad_B {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (d : Fin m → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (B A d *ᵥ x) = ∑ k : Fin m, d k * (col A k ⬝ᵥ x) ^ 2 := by
  have h1 : B A d *ᵥ x = A *ᵥ (diagonal d *ᵥ (Aᵀ *ᵥ x)) := by
    simp [B, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, AT_mulVec_apply]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma B_symm {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (d : Fin m → ℝ) :
    (B A d)ᵀ = B A d := by
  simp [B, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Under Assumption 1.1 and `d > 0`, `B(d)` is invertible. -/
lemma B_isUnit {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A)
    (d : Fin m → ℝ) (hd : ∀ i, 0 < d i) : IsUnit (B A d) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  suffices H : ∀ x, B A d *ᵥ x = 0 → x = 0 by
    intro x y hxy
    have := H (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
    exact sub_eq_zero.1 this
  intro x hx
  have hq : ∑ k : Fin m, d k * (col A k ⬝ᵥ x) ^ 2 = 0 := by
    rw [← quad_B, hx, dotProduct_zero]
  have hall : ∀ k, col A k ⬝ᵥ x = 0 := by
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
      have := hd k; positivity)).1 hq k (Finset.mem_univ _)
    have hdk := (hd k).ne'
    have : (col A k ⬝ᵥ x) ^ 2 = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hdk
      · exact h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  obtain ⟨lam, -, hlam⟩ := hA.1 x
  have hATx : Aᵀ *ᵥ x = 0 := by
    funext k; rw [AT_mulVec_apply]; exact hall k
  have : x ⬝ᵥ x = 0 := by
    calc x ⬝ᵥ x = x ⬝ᵥ (A *ᵥ lam) := by rw [hlam]
      _ = 0 := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hATx, zero_dotProduct]
  exact dotProduct_self_eq_zero.1 this

lemma slab_pos {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (hA : Assumption11 A)
    (hd : ∀ i, 0 < d i) (hf : 0 < f A u d ell) (i : Fin m) :
    0 < slabRadius A u d ell i := by
  set w := (B A d)⁻¹ *ᵥ col A i with hw
  have hBu := B_isUnit A hA d hd
  have hBw : B A d *ᵥ w = col A i := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hBu),
      Matrix.one_mulVec]
  set q := col A i ⬝ᵥ w with hq
  have hq_eq : q = ∑ k : Fin m, d k * (col A k ⬝ᵥ w) ^ 2 := by
    rw [← quad_B, hBw, hq, dotProduct_comm]
  have hq_nonneg : 0 ≤ q := by
    rw [hq_eq]; exact Finset.sum_nonneg fun k _ => by have := hd k; positivity
  have hqpos : 0 < q := by
    rcases hq_nonneg.eq_or_lt with h | h
    · exfalso
      have hq0 : ∑ k : Fin m, d k * (col A k ⬝ᵥ w) ^ 2 = 0 := by rw [← hq_eq, h]
      have hall : ∀ k, col A k ⬝ᵥ w = 0 := by
        intro k
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
          have := hd k; positivity)).1 hq0 k (Finset.mem_univ _)
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (hd k).ne'
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      have hATw : Aᵀ *ᵥ w = 0 := by
        funext k; rw [AT_mulVec_apply]; exact hall k
      have hB0 : B A d *ᵥ w = 0 := by
        simp [B, ← Matrix.mulVec_mulVec, hATw]
      have hcol : col A i = 0 := by rw [← hBw, hB0]
      have h1 := hA.2 i
      have : ∀ k, A k i = 0 := fun k => congrFun hcol k
      simp [this] at h1
    · exact h
  exact Real.sqrt_pos.2 (mul_pos hf hqpos)


lemma dot_AT (A : Matrix (Fin n) (Fin m) ℝ) (z : Fin m → ℝ) (x : Fin n → ℝ) :
    z ⬝ᵥ (Aᵀ *ᵥ x) = (A *ᵥ z) ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma B_mulVec (A : Matrix (Fin n) (Fin m) ℝ) (d : Fin m → ℝ) (x : Fin n → ℝ) :
    B A d *ᵥ x = A *ᵥ (d * (Aᵀ *ᵥ x)) := by
  have : diagonal d *ᵥ (Aᵀ *ᵥ x) = d * (Aᵀ *ᵥ x) := by
    funext k; simp [Matrix.mulVec_diagonal]
  rw [← this]; simp [B, Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma B_smul (A : Matrix (Fin n) (Fin m) ℝ) (c : ℝ) (d : Fin m → ℝ) :
    B A (c • d) = c • B A d := by
  simp [B, Matrix.diagonal_smul]

lemma inv_smul_any (M : Matrix (Fin n) (Fin n) ℝ) {c : ℝ} (hc : c ≠ 0) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases h : IsUnit M.det
  · exact Matrix.inv_eq_left_inv (by simp [smul_smul, hc, Matrix.nonsing_inv_mul _ h])
  · have h2 : ¬ IsUnit (c • M).det := by
      rw [Matrix.det_smul]
      intro hu
      apply h
      rw [isUnit_iff_ne_zero] at hu ⊢
      intro h0; apply hu; rw [h0, mul_zero]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h2, smul_zero]

lemma y_smul (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0) :
    y A u (c • d) ell = y A u d ell := by
  unfold y
  rw [B_smul, inv_smul_any _ hc]
  have : (c • d) * r u ell = c • (d * r u ell) := by
    funext i; simp [mul_assoc]
  rw [this, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

lemma t_smul (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0) :
    t A u (c • d) ell = t A u d ell := by
  unfold t; rw [y_smul A u d ell hc]

lemma f_smul (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0) :
    f A u (c • d) ell = c * f A u d ell := by
  unfold f
  rw [t_smul A u d ell hc, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp [mul_assoc]

lemma slab_smul (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0)
    (i : Fin m) : slabRadius A u (c • d) ell i = slabRadius A u d ell i := by
  unfold slabRadius
  rw [f_smul A u d ell hc, B_smul, inv_smul_any _ hc, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]
  congr 1
  field_simp

lemma Lb_smul (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0)
    (i : Fin m) : Lb A u (c • d) ell i = Lb A u d ell i := by
  unfold Lb; rw [y_smul A u d ell hc, slab_smul A u d ell hc]


lemma inv_mulVec_of (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M) {x b : Fin n → ℝ}
    (h : M *ᵥ x = b) : M⁻¹ *ᵥ b = x := by
  rw [← h, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hM), Matrix.one_mulVec]

lemma mul_inv_B (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) : B A d * (B A d)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (B_isUnit A hA d hd))

lemma A_single (A : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (c : ℝ) :
    A *ᵥ (Pi.single j c : Fin m → ℝ) = c • col A j := by
  funext k
  simp [Matrix.mulVec, dotProduct, col, Pi.single_apply, mul_comm]

lemma r_shift (u ell : Fin m → ℝ) (j : Fin m) (β : ℝ) :
    r u (ell + β • Pi.single j 1) = r u ell + (β / 2) • Pi.single j 1 := by
  funext k; simp only [r, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma v_shift (u ell : Fin m → ℝ) (j : Fin m) (β : ℝ) :
    v u (ell + β • Pi.single j 1) = v u ell - (β / 2) • Pi.single j 1 := by
  funext k; simp only [v, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- Proposition D.2, (46). -/
lemma y_shift (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) (j : Fin m) (β : ℝ) :
    y A u d (ell + β • Pi.single j 1) =
      y A u d ell + (β / 2 * d j) • ((B A d)⁻¹ *ᵥ col A j) := by
  unfold y
  rw [r_shift]
  have : d * (r u ell + (β / 2) • Pi.single j 1) =
      d * r u ell + (Pi.single j (β / 2 * d j) : Fin m → ℝ) := by
    funext k
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with h
    · subst h; ring
    · ring
  rw [this, Matrix.mulVec_add, Matrix.mulVec_add, A_single, Matrix.mulVec_smul]

/-- Proposition D.2, (47). -/
lemma t_shift (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) (j : Fin m) (β : ℝ) :
    t A u d (ell + β • Pi.single j 1) =
      t A u d ell + (β / 2 * d j) • (Aᵀ *ᵥ ((B A d)⁻¹ *ᵥ col A j)) - (β / 2) • Pi.single j 1 := by
  unfold t
  rw [y_shift, r_shift, Matrix.mulVec_add, Matrix.mulVec_smul]
  abel

/-- `A D t(d,ℓ) = 0`. -/
lemma ADt (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (u d ell : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) : A *ᵥ (d * t A u d ell) = 0 := by
  have hBy : B A d *ᵥ y A u d ell = A *ᵥ (d * r u ell) := by
    rw [y, Matrix.mulVec_mulVec, mul_inv_B A hA d hd, Matrix.one_mulVec]
  have : t A u d ell = Aᵀ *ᵥ y A u d ell - r u ell := rfl
  rw [this, mul_sub, Matrix.mulVec_sub, ← B_mulVec, hBy, sub_self]

lemma ADATw (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (b : Fin n → ℝ) :
    A *ᵥ (d * (Aᵀ *ᵥ ((B A d)⁻¹ *ᵥ b))) = b := by
  rw [← B_mulVec, Matrix.mulVec_mulVec, mul_inv_B A hA d hd, Matrix.one_mulVec]

/-- Proposition D.2, (48). -/
lemma f_shift (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (u d ell : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (j : Fin m) (β : ℝ) :
    f A u d (ell + β • Pi.single j 1) =
      f A u d ell + β * (t A u d ell j - v u ell j) * d j +
        1 / 4 * β ^ 2 * d j ^ 2 * (col A j ⬝ᵥ ((B A d)⁻¹ *ᵥ col A j)) := by
  set w := (B A d)⁻¹ *ᵥ col A j with hw
  set g := Aᵀ *ᵥ w with hg
  set tt := t A u d ell with htt
  set vv := v u ell with hvv
  have hS1 : ∑ k, d k * tt k * g k = 0 := by
    have := dot_AT A (d * tt) w
    rw [ADt A hA u d ell hd, zero_dotProduct] at this
    rw [← this]; simp [dotProduct, hg]
  have hS2 : ∑ k, d k * g k * g k = col A j ⬝ᵥ w := by
    have := dot_AT A (d * g) w
    rw [hg, ADATw A hA d hd] at this
    rw [← this]; simp [dotProduct, hg]
  have hgj : g j = col A j ⬝ᵥ w := by rw [hg, AT_mulVec_apply]
  unfold f
  rw [t_shift, v_shift, ← htt, ← hvv, ← hw, ← hg]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have e1 : ∀ k, d k * (vv k - β / 2 * (if k = j then 1 else 0)) ^ 2 =
      d k * vv k ^ 2 - β * (if k = j then d k * vv k else 0) +
        β ^ 2 / 4 * (if k = j then d k else 0) := by
    intro k; split_ifs <;> ring
  have e2 : ∀ k, d k * (tt k + β / 2 * d j * g k - β / 2 * (if k = j then 1 else 0)) ^ 2 =
      d k * tt k ^ 2 + β * d j * (d k * tt k * g k) - β * (if k = j then d k * tt k else 0) +
        β ^ 2 / 4 * d j ^ 2 * (d k * g k * g k) -
        β ^ 2 / 2 * d j * (if k = j then d k * g k else 0) +
        β ^ 2 / 4 * (if k = j then d k else 0) := by
    intro k; split_ifs <;> ring
  simp only [e1, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hS1, hS2]
  rw [hgj]
  ring

lemma q_pos {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (i : Fin m) : 0 < col A i ⬝ᵥ ((B A d)⁻¹ *ᵥ col A i) := by
  set w := (B A d)⁻¹ *ᵥ col A i with hw
  have hBu := B_isUnit A hA d hd
  have hBw : B A d *ᵥ w = col A i := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hBu),
      Matrix.one_mulVec]
  set q := col A i ⬝ᵥ w with hq
  have hq_eq : q = ∑ k : Fin m, d k * (col A k ⬝ᵥ w) ^ 2 := by
    rw [← quad_B, hBw, hq, dotProduct_comm]
  have hq_nonneg : 0 ≤ q := by
    rw [hq_eq]; exact Finset.sum_nonneg fun k _ => by have := hd k; positivity
  have hqpos : 0 < q := by
    rcases hq_nonneg.eq_or_lt with h | h
    · exfalso
      have hq0 : ∑ k : Fin m, d k * (col A k ⬝ᵥ w) ^ 2 = 0 := by rw [← hq_eq, h]
      have hall : ∀ k, col A k ⬝ᵥ w = 0 := by
        intro k
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
          have := hd k; positivity)).1 hq0 k (Finset.mem_univ _)
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (hd k).ne'
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      have hATw : Aᵀ *ᵥ w = 0 := by
        funext k; rw [AT_mulVec_apply]; exact hall k
      have hB0 : B A d *ᵥ w = 0 := by
        simp [B, ← Matrix.mulVec_mulVec, hATw]
      have hcol : col A i = 0 := by rw [← hBw, hB0]
      have h1 := hA.2 i
      have : ∀ k, A k i = 0 := fun k => congrFun hcol k
      simp [this] at h1
    · exact h
  exact hqpos



/-- `γ_i(d,ℓ)^2 = f(d,ℓ) a_iᵀB⁻¹a_i` when `f ≥ 0`. -/
lemma slab_sq (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (u d ell : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (hf : 0 ≤ f A u d ell) (i : Fin m) :
    slabRadius A u d ell i ^ 2 = f A u d ell * (col A i ⬝ᵥ ((B A d)⁻¹ *ᵥ col A i)) := by
  have hq := (q_pos A hA d hd i).le
  unfold slabRadius
  rw [Real.sq_sqrt (mul_nonneg hf hq)]


lemma t_sub_v (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) (j : Fin m) :
    t A u d ell j - v u ell j = col A j ⬝ᵥ y A u d ell - u j := by
  simp only [t, v, r, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, AT_mulVec_apply]
  ring

lemma ell1_eq (A : Matrix (Fin n) (Fin m) ℝ) (u d ell : Fin m → ℝ) (j : Fin m) :
    ell1 A u d ell j = ell + (-(2 * (col A j ⬝ᵥ y A u d ell - u j) /
      (d j * slabRadius A u d ell j ^ 2))) • Pi.single j 1 := by
  rw [ell1, t_sub_v, neg_smul, ← sub_eq_add_neg]

lemma By_eq (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (u d ell : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) : B A d *ᵥ y A u d ell = A *ᵥ (d * r u ell) := by
  rw [y, Matrix.mulVec_mulVec, mul_inv_B A hA d hd, Matrix.one_mulVec]

lemma Bw_eq (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (b : Fin n → ℝ) : B A d *ᵥ ((B A d)⁻¹ *ᵥ b) = b := by
  rw [Matrix.mulVec_mulVec, mul_inv_B A hA d hd, Matrix.one_mulVec]

lemma mul_single_add (D w : Fin m → ℝ) (j : Fin m) (c : ℝ) :
    (D + c • Pi.single j 1) * w = D * w + (Pi.single j (c * w j) : Fin m → ℝ) := by
  funext k
  simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs with h
  · subst h; ring
  · ring

lemma B_dshift_mulVec (A : Matrix (Fin n) (Fin m) ℝ) (D : Fin m → ℝ) (j : Fin m) (c : ℝ)
    (x : Fin n → ℝ) :
    B A (D + c • Pi.single j 1) *ᵥ x = B A D *ᵥ x + (c * (col A j ⬝ᵥ x)) • col A j := by
  rw [B_mulVec, B_mulVec, mul_single_add, Matrix.mulVec_add, A_single, AT_mulVec_apply]

lemma pos_dshift {D : Fin m → ℝ} (hD : ∀ i, 0 < D i) (j : Fin m) {c : ℝ} (hc : 0 ≤ c) :
    ∀ i, 0 < (D + c • Pi.single j 1 : Fin m → ℝ) i := by
  intro i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have := hD i
  split_ifs <;> nlinarith

/-- Proposition D.1, (43). -/
lemma y_dshift (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (u D ell : Fin m → ℝ)
    (hD : ∀ i, 0 < D i) (j : Fin m) {c : ℝ} (hc : 0 ≤ c) :
    y A u (D + c • Pi.single j 1) ell = y A u D ell -
      (c / (1 + c * (col A j ⬝ᵥ ((B A D)⁻¹ *ᵥ col A j))) * t A u D ell j) •
        ((B A D)⁻¹ *ᵥ col A j) := by
  set w := (B A D)⁻¹ *ᵥ col A j with hw
  set q := col A j ⬝ᵥ w with hq
  have hq0 : 0 < q := q_pos A hA D hD j
  have h1 : 0 < 1 + c * q := by positivity
  set s := c / (1 + c * q) * t A u D ell j with hs
  have hD2 := pos_dshift hD j hc
  apply inv_mulVec_of _ (B_isUnit A hA _ hD2)
  have htj : t A u D ell j = col A j ⬝ᵥ y A u D ell - r u ell j := by
    simp only [t, Pi.sub_apply, AT_mulVec_apply]
  have key : -s + c * (col A j ⬝ᵥ y A u D ell - s * q) = c * r u ell j := by
    rw [hs, htj]; field_simp; ring
  rw [B_dshift_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, By_eq A hA u D ell hD,
    Bw_eq A hA D hD, dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hq, mul_single_add,
    Matrix.mulVec_add, A_single]
  rw [← key]
  module

lemma t_dshift (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (u D ell : Fin m → ℝ)
    (hD : ∀ i, 0 < D i) (j : Fin m) {c : ℝ} (hc : 0 ≤ c) :
    t A u (D + c • Pi.single j 1) ell = t A u D ell -
      (c / (1 + c * (col A j ⬝ᵥ ((B A D)⁻¹ *ᵥ col A j))) * t A u D ell j) •
        (Aᵀ *ᵥ ((B A D)⁻¹ *ᵥ col A j)) := by
  unfold t
  rw [y_dshift A hA u D ell hD j hc, Matrix.mulVec_sub, Matrix.mulVec_smul]
  unfold t
  abel

/-- Proposition D.1: `aᵀ B(D + c e_j)⁻¹ a = q/(1+cq)`. -/
lemma q_dshift (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (D : Fin m → ℝ)
    (hD : ∀ i, 0 < D i) (j : Fin m) {c : ℝ} (hc : 0 ≤ c) :
    col A j ⬝ᵥ ((B A (D + c • Pi.single j 1))⁻¹ *ᵥ col A j) =
      col A j ⬝ᵥ ((B A D)⁻¹ *ᵥ col A j) / (1 + c * (col A j ⬝ᵥ ((B A D)⁻¹ *ᵥ col A j))) := by
  set w := (B A D)⁻¹ *ᵥ col A j with hw
  set q := col A j ⬝ᵥ w with hq
  have hq0 : 0 < q := q_pos A hA D hD j
  have h1 : 0 < 1 + c * q := by positivity
  have hD2 := pos_dshift hD j hc
  have : (B A (D + c • Pi.single j 1))⁻¹ *ᵥ col A j = (1 / (1 + c * q)) • w := by
    apply inv_mulVec_of _ (B_isUnit A hA _ hD2)
    rw [B_dshift_mulVec, Matrix.mulVec_smul, Bw_eq A hA D hD, dotProduct_smul, smul_eq_mul,
      ← hq, ← add_smul]
    rw [show 1 / (1 + c * q) + c * (1 / (1 + c * q) * q) = 1 by field_simp, one_smul]
  rw [this, dotProduct_smul, smul_eq_mul, ← hq]
  field_simp

/-- Proposition D.1, (42). -/
lemma f_dshift (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (u D ell : Fin m → ℝ)
    (hD : ∀ i, 0 < D i) (j : Fin m) {c : ℝ} (hc : 0 ≤ c) :
    f A u (D + c • Pi.single j 1) ell = f A u D ell + c * v u ell j ^ 2 -
      c / (1 + c * (col A j ⬝ᵥ ((B A D)⁻¹ *ᵥ col A j))) * t A u D ell j ^ 2 := by
  set w := (B A D)⁻¹ *ᵥ col A j with hw
  set q := col A j ⬝ᵥ w with hq
  have hq0 : 0 < q := q_pos A hA D hD j
  have h1 : 0 < 1 + c * q := by positivity
  set g := Aᵀ *ᵥ w with hg
  set tt := t A u D ell with htt
  set vv := v u ell with hvv
  have hS1 : ∑ k, D k * tt k * g k = 0 := by
    have := dot_AT A (D * tt) w
    rw [ADt A hA u D ell hD, zero_dotProduct] at this
    rw [← this]; simp [dotProduct, hg]
  have hS2 : ∑ k, D k * g k * g k = q := by
    have := dot_AT A (D * g) w
    rw [hg, ADATw A hA D hD] at this
    rw [hq, ← this]; simp [dotProduct, hg]
  have hgj : g j = q := by rw [hg, AT_mulVec_apply]
  set s := c / (1 + c * q) * tt j with hs
  unfold f
  rw [t_dshift A hA u D ell hD j hc, ← htt, ← hvv, ← hw, ← hq, ← hg, ← hs]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have e1 : ∀ k, (D k + c * (if k = j then 1 else 0)) * vv k ^ 2 =
      D k * vv k ^ 2 + c * (if k = j then vv k ^ 2 else 0) := by
    intro k; split_ifs <;> ring
  have e2 : ∀ k, (D k + c * (if k = j then 1 else 0)) * (tt k - s * g k) ^ 2 =
      D k * tt k ^ 2 - 2 * s * (D k * tt k * g k) + s ^ 2 * (D k * g k * g k) +
        c * (if k = j then (tt k - s * g k) ^ 2 else 0) := by
    intro k; split_ifs <;> ring
  simp only [e1, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hS1, hS2, hgj]
  rw [hs]
  field_simp
  ring

/-- `m ≥ 2` under Assumption 1.1 whenever `m ≠ 0`. -/
lemma two_le_m {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A)
    (j : Fin m) : 2 ≤ m := by
  by_contra hm
  have hm1 : m = 1 := by have := j.pos; omega
  subst hm1
  obtain ⟨lam, hlam0, hlam⟩ := hA.1 (fun k => - A k 0)
  have h1 := hA.2 0
  have hk : ∀ k, (lam 0 + 1) * A k 0 = 0 := by
    intro k
    have := congrFun hlam k
    simp [Matrix.mulVec, dotProduct] at this
    linarith
  have hl : 0 < lam 0 + 1 := by have := hlam0 0; simp at this; linarith
  have : ∀ k, A k 0 = 0 := fun k => by
    rcases mul_eq_zero.1 (hk k) with h | h
    · linarith
    · exact h
  simp [this] at h1


/-- The alternative description (13) of the ellipsoid's quadratic form. -/
lemma quad_E (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (u d ell : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (x : Fin n → ℝ) :
    ∑ i, d i * ((Aᵀ *ᵥ x) i - ell i) * ((Aᵀ *ᵥ x) i - u i) =
      (x - y A u d ell) ⬝ᵥ (B A d *ᵥ (x - y A u d ell)) - f A u d ell := by
  set z := x - y A u d ell with hz
  set tt := t A u d ell with htt
  have hS : ∑ i, d i * tt i * (col A i ⬝ᵥ z) = 0 := by
    have := dot_AT A (d * tt) z
    rw [ADt A hA u d ell hd, zero_dotProduct] at this
    rw [← this]; simp [dotProduct, AT_mulVec_apply]
  have hx : ∀ i, (Aᵀ *ᵥ x) i = col A i ⬝ᵥ z + tt i + r u ell i := by
    intro i
    simp only [hz, htt, t, Pi.sub_apply, AT_mulVec_apply, dotProduct_sub]; ring
  rw [quad_B]
  unfold f
  rw [← htt]
  simp only [hx]
  have e : ∀ i, d i * (col A i ⬝ᵥ z + tt i + r u ell i - ell i) *
      (col A i ⬝ᵥ z + tt i + r u ell i - u i) =
      d i * (col A i ⬝ᵥ z) ^ 2 + 2 * (d i * tt i * (col A i ⬝ᵥ z)) + d i * tt i ^ 2 -
        d i * v u ell i ^ 2 := by
    intro i
    simp only [r, v, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]; ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hS]
  ring

lemma certLBi_col (A : Matrix (Fin n) (Fin m) ℝ) (u ell : Fin m → ℝ)
    (Lam : Matrix (Fin m) (Fin m) ℝ) (h : CertLB A u ell Lam) (k : Fin m) :
    CertLBi A u k (ell k) (Lam.col k) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun i => h2 i k, ?_⟩
  · funext r
    have := congrFun (congrFun h1 r) k
    simp only [Matrix.mul_apply, Matrix.neg_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Pi.neg_apply, col]
    rw [this]
  · have := h3 k
    simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply] at this
    simp only [dotProduct, Matrix.col_apply]
    exact this

lemma certLB_mono {A : Matrix (Fin n) (Fin m) ℝ} {u ell ell' : Fin m → ℝ}
    {Lam : Matrix (Fin m) (Fin m) ℝ} (h : CertLB A u ell Lam) (hle : ell' ≤ ell) :
    CertLB A u ell' Lam := ⟨h.1, h.2.1, hle.trans h.2.2⟩

/-- Remark 1.1. -/
lemma alt_of_gap (A : Matrix (Fin n) (Fin m) ℝ) (u : Fin m → ℝ) (j : Fin m) (l : ℝ)
    (lam : Fin m → ℝ) (h : CertLBi A u j l lam) (hgap : u j < l) :
    IsAlt A u (lam + Pi.single j 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mulVec_add, h1, A_single, one_smul, neg_add_cancel]
  · intro i
    simp only [Pi.add_apply, Pi.zero_apply, Pi.single_apply]
    have := h2 i
    split_ifs <;> simp at this ⊢ <;> linarith
  · rw [dotProduct_add, dotProduct_comm u lam]
    simp only [dotProduct_single, mul_one]
    linarith

lemma exists_viol {A : Matrix (Fin n) (Fin m) ℝ} {u : Fin m → ℝ} {x : Fin n → ℝ}
    (h : ¬ IsFeasible A u x) : ∃ i, 0 < col A i ⬝ᵥ x - u i := by
  unfold IsFeasible at h
  rw [Pi.le_def] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by rw [AT_mulVec_apply] at hi; linarith⟩


/-- Feasible points lie in the ellipsoid: `(x-y)ᵀB(x-y) ≤ f`. -/
lemma feas_in_E (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (u d ell : Fin m → ℝ)
    (Lam : Matrix (Fin m) (Fin m) ℝ) (hd : ∀ i, 0 < d i) (hcert : CertLB A u ell Lam)
    (x : Fin n → ℝ) (hx : IsFeasible A u x) :
    (x - y A u d ell) ⬝ᵥ (B A d *ᵥ (x - y A u d ell)) ≤ f A u d ell := by
  have hlow : ∀ i, ell i ≤ (Aᵀ *ᵥ x) i := by
    intro i
    obtain ⟨h1, h2, h3⟩ := certLBi_col A u ell Lam hcert i
    have : (Aᵀ *ᵥ x) i = -(Lam.col i ⬝ᵥ (Aᵀ *ᵥ x)) := by
      rw [dot_AT, h1, AT_mulVec_apply, neg_dotProduct, neg_neg]
    rw [this]
    have : Lam.col i ⬝ᵥ (Aᵀ *ᵥ x) ≤ Lam.col i ⬝ᵥ u := by
      simp only [dotProduct]
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hx k) (h2 k)
    linarith
  have hQ : ∑ i, d i * ((Aᵀ *ᵥ x) i - ell i) * ((Aᵀ *ᵥ x) i - u i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have h1 := hlow i; have h2 := hx i; have h3 := hd i
    have ha : 0 ≤ (Aᵀ *ᵥ x) i - ell i := by linarith
    have hb : (Aᵀ *ᵥ x) i - u i ≤ 0 := by linarith
    have := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h3.le ha) hb
    linarith
  rw [quad_E A hA u d ell hd x] at hQ
  linarith

/-- Cauchy–Schwarz in the `B(d)` geometry: `(aᵢᵀh)² ≤ (aᵢᵀB⁻¹aᵢ)(hᵀBh)`. -/
lemma cs_B (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (i : Fin m) (h : Fin n → ℝ) :
    (col A i ⬝ᵥ h) ^ 2 ≤ (col A i ⬝ᵥ ((B A d)⁻¹ *ᵥ col A i)) * (h ⬝ᵥ (B A d *ᵥ h)) := by
  set w := (B A d)⁻¹ *ᵥ col A i with hw
  have hBw : B A d *ᵥ w = col A i := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (B_isUnit A hA d hd)), Matrix.one_mulVec]
  have h1 : col A i ⬝ᵥ h = ∑ k, (Real.sqrt (d k) * (col A k ⬝ᵥ w)) *
      (Real.sqrt (d k) * (col A k ⬝ᵥ h)) := by
    rw [← hBw, B_mulVec, ← dot_AT, dotProduct_comm]
    simp only [dotProduct, Pi.mul_apply, AT_mulVec_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := Real.mul_self_sqrt (hd k).le
    linear_combination (-1 : ℝ) * (∑ x, col A k x * h x) * (∑ x, col A k x * w x) * this
  have h2 : col A i ⬝ᵥ w = ∑ k, (Real.sqrt (d k) * (col A k ⬝ᵥ w)) ^ 2 := by
    rw [← hBw, dotProduct_comm, quad_B]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, Real.sq_sqrt (hd k).le]
  have h3 : h ⬝ᵥ (B A d *ᵥ h) = ∑ k, (Real.sqrt (d k) * (col A k ⬝ᵥ h)) ^ 2 := by
    rw [quad_B]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, Real.sq_sqrt (hd k).le]
  rw [h1, h2, h3]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma unit_dot (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A) (i k : Fin m) :
    |col A k ⬝ᵥ col A i| ≤ 1 := by
  have hi := hA.2 i
  have hk := hA.2 k
  have hii : col A i ⬝ᵥ col A i = 1 := by simpa [dotProduct, col, sq] using hi
  have hkk : col A k ⬝ᵥ col A k = 1 := by simpa [dotProduct, col, sq] using hk
  have p1 := dotProduct_self_star_nonneg (col A k - col A i)
  have p2 := dotProduct_self_star_nonneg (col A k + col A i)
  simp only [star_trivial] at p1 p2
  simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add] at p1 p2
  rw [dotProduct_comm (col A i) (col A k)] at p1 p2
  rw [abs_le]; constructor <;> linarith

theorem prop52 (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (i : Fin m)
    (hmax : ∀ h : Fin m, col A h ⬝ᵥ y A u d ell - u h ≤
      col A i ⬝ᵥ y A u d ell - u i)
    (hsmall : slabRadius A u d ell i < tau A u) :
    IsAlt A u (lamTilde A u d ell Lam i + Pi.single i 1) := by
  set γ := slabRadius A u d ell i with hγ
  have hγ0 : 0 ≤ γ := Real.sqrt_nonneg _
  set g : (Fin n → ℝ) → ℝ := fun x => ⨅ k : Fin m, (u k - col A k ⬝ᵥ x) with hg
  have hzs : zStar A u = sSup (Set.range g) := rfl
  by_cases hP : ∃ x, IsFeasible A u x
  · exfalso
    obtain ⟨x0, hx0⟩ := hP
    by_cases hbdd : BddAbove (Set.range g)
    swap
    · have : zStar A u = 0 := by rw [hzs]; exact Real.sSup_of_not_bddAbove hbdd
      have : tau A u = 0 := by simp [tau, this]
      linarith
    have hne : Nonempty (Fin m) := ⟨i⟩
    have hgx0 : 0 ≤ g x0 := by
      apply le_ciInf; intro k; have := hx0 k; rw [AT_mulVec_apply] at this; linarith
    have hz0 : 0 ≤ zStar A u := hgx0.trans (le_csSup hbdd ⟨x0, rfl⟩)
    have htau : tau A u = zStar A u := abs_of_nonneg hz0
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_lt_of_lt_csSup (Set.range_nonempty g)
      (show γ < sSup (Set.range g) by rw [← hzs, ← htau]; exact hsmall)
    set s := g x with hs
    have hgle : ∀ k, col A k ⬝ᵥ x ≤ u k - s := by
      intro k; have := ciInf_le (Finite.bddBelow_range fun k : Fin m => (u k - col A k ⬝ᵥ x)) k
      simp only [hs, hg] at this ⊢; linarith
    have hfeas : ∀ σ : ℝ, |σ| ≤ s → IsFeasible A u (x + σ • col A i) := by
      intro σ hσ k
      rw [AT_mulVec_apply, dotProduct_add, dotProduct_smul, smul_eq_mul]
      have h1 := hgle k
      have h2 := unit_dot A hA i k
      have h3 : σ * (col A k ⬝ᵥ col A i) ≤ s := by
        calc σ * (col A k ⬝ᵥ col A i) ≤ |σ * (col A k ⬝ᵥ col A i)| := le_abs_self _
          _ = |σ| * |col A k ⬝ᵥ col A i| := abs_mul _ _
          _ ≤ s * 1 := mul_le_mul hσ h2 (abs_nonneg _) (by linarith)
          _ = s := mul_one _
      linarith
    have hs0 : 0 < s := lt_of_le_of_lt hγ0 hx
    have hslab : ∀ σ : ℝ, |σ| ≤ s →
        |col A i ⬝ᵥ (x + σ • col A i - y A u d ell)| ≤ γ := by
      intro σ hσ
      have hE := feas_in_E A hA u d ell Lam hd hcert _ (hfeas σ hσ)
      rw [hf] at hE
      have hcs := cs_B A hA d hd i (x + σ • col A i - y A u d ell)
      have hq : γ ^ 2 = col A i ⬝ᵥ ((B A d)⁻¹ *ᵥ col A i) := by
        rw [hγ, slabRadius, hf, one_mul, Real.sq_sqrt (by
          have := q_pos A hA d hd i; linarith)]
      have hq0 : 0 ≤ col A i ⬝ᵥ ((B A d)⁻¹ *ᵥ col A i) := by rw [← hq]; positivity
      have : (col A i ⬝ᵥ (x + σ • col A i - y A u d ell)) ^ 2 ≤ γ ^ 2 := by
        rw [hq]; calc _ ≤ _ := hcs
          _ ≤ (col A i ⬝ᵥ ((B A d)⁻¹ *ᵥ col A i)) * 1 := by gcongr
          _ = _ := mul_one _
      exact abs_le_of_sq_le_sq' this hγ0 |> fun h => abs_le.2 h
    have hii : col A i ⬝ᵥ col A i = 1 := by simpa [dotProduct, col, sq] using hA.2 i
    have hp := hslab s (by rw [abs_of_pos hs0])
    have hm := hslab (-s) (by rw [abs_neg, abs_of_pos hs0])
    rw [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, hii] at hp hm
    rw [abs_le] at hp hm
    linarith [hp.2, hm.1]
  · -- (P) is empty: the most violated constraint is violated by at least τ
    have hz := (proposition_4_1_b A u hA hP).1
    have hbdd : BddAbove (Set.range g) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨z, rfl⟩
      obtain ⟨k, hk⟩ := exists_viol (fun h => hP ⟨z, h⟩)
      have := ciInf_le (Finite.bddBelow_range fun k : Fin m => (u k - col A k ⬝ᵥ z)) k
      simp only [hg] at this ⊢
      linarith
    have h1 : g (y A u d ell) ≤ zStar A u := le_csSup hbdd ⟨_, rfl⟩
    have hne : Nonempty (Fin m) := ⟨i⟩
    have h2 : u i - col A i ⬝ᵥ y A u d ell ≤ g (y A u d ell) :=
      le_ciInf fun k => by have := hmax k; linarith
    have hviol : tau A u ≤ col A i ⬝ᵥ y A u d ell - u i := by rw [hz]; linarith
    have hgap : u i < Lb A u d ell i := by simp only [Lb]; rw [← hγ]; linarith
    exact alt_of_gap A u i _ _ (proposition_5_1 A u d ell Lam hA hd hcert hf i) hgap

end OEAProp52
end OblivEllipsoid.Infeas

open OblivEllipsoid.Infeas in
theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (i : Fin m)
    (hmax : ∀ h : Fin m, OblivEllipsoid.Infeas.col A h ⬝ᵥ y A u d ell - u h ≤
      OblivEllipsoid.Infeas.col A i ⬝ᵥ y A u d ell - u i)
    (hsmall : slabRadius A u d ell i < tau A u) :
    IsAlt A u (lamTilde A u d ell Lam i + Pi.single i 1) :=
  OblivEllipsoid.Infeas.OEAProp52.prop52 A u d ell Lam hA hd hcert hf i hmax hsmall
