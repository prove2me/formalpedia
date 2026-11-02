-- Prove2me | solution 1 for OblivEllipsoid.Infeas.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:53:11.228855+00:00
-- url     : https://prove2.me/submissions/9f2af798-d543-4622-ac69-b4d98dc2379d

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas
namespace OEAThm61

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


lemma alg61 (m V g Dj c b q1 : ℝ) (hm : 2 ≤ m) (hg : 0 < g) (hDj : 0 < Dj) (hq1 : g ^ 2 = q1)
    (hc : c = 2 / (m - 1) * (1 / g ^ 2))
    (hb : b = 2 * (2 * V - g) / ((m - 1) * Dj * g ^ 2 + 2)) :
    1 + c * V ^ 2 - c / (1 + c * q1) * V ^ 2 + b * (V - c / (1 + c * q1) * V * q1 - V) * (Dj + c) +
      1 / 4 * b ^ 2 * (Dj + c) ^ 2 * (q1 / (1 + c * q1)) = m ^ 2 / (m ^ 2 - 1) := by
  have hm1 : m - 1 ≠ 0 := by linarith
  have hm1' : 0 < m - 1 := by linarith
  have hcq : 1 + c * q1 = (m + 1) / (m - 1) := by
    rw [hc, ← hq1]; field_simp; ring
  have hDc : Dj + c = ((m - 1) * Dj * g ^ 2 + 2) / ((m - 1) * g ^ 2) := by
    rw [hc]; field_simp
  have hden : 0 < (m - 1) * Dj * g ^ 2 + 2 := by positivity
  rw [hcq, hDc, hb, hc, ← hq1]
  have hm2 : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hm3 : m + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem thm61 (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (j : Fin m)
    (hviol : 0 < col A j ⬝ᵥ y A u d ell - u j)
    (hle : col A j ⬝ᵥ y A u d ell - u j ≤ slabRadius A u d ell j)
    (hf1 : 0 < f A u d (ell1 A u d ell j)) :
    ∃ alpha : ℝ, (((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2) < alpha ∧
      d3 A u d ell j = alpha •
        (d + ((2 / ((m : ℝ) - 1)) *
          (1 / slabRadius A u d ell j ^ 2)) • Pi.single j 1) := by
  have hm := two_le_m A hA j
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set q := col A j ⬝ᵥ ((B A d)⁻¹ *ᵥ col A j) with hq
  have hqpos : 0 < q := q_pos A hA d hd j
  set γ := slabRadius A u d ell j with hγ
  have hγ2 : γ ^ 2 = q := by rw [hγ, slab_sq A hA u d ell hd (by rw [hf]; norm_num), hf, one_mul]
  set δ := col A j ⬝ᵥ y A u d ell - u j with hδ
  have hdj := hd j
  set β1 := -(2 * δ / (d j * γ ^ 2)) with hβ1
  have he1 : ell1 A u d ell j = ell + β1 • Pi.single j 1 := ell1_eq A u d ell j
  set e1 := ell1 A u d ell j with he1def
  have hf1eq : f A u d e1 = 1 - δ ^ 2 / q := by
    rw [he1, f_shift A hA u d ell hd j β1, hf, t_sub_v, ← hδ, ← hq, hβ1, hγ2]
    field_simp
    ring
  set f1 := f A u d e1 with hf1def
  have hf1lt : f1 < 1 := by
    rw [hf1eq]; have : 0 < δ ^ 2 / q := by positivity
    linarith
  -- the normalized weights D = d⁽¹⁾
  have hc1 : (1 / f1) ≠ 0 := by positivity
  set D := (1 / f1) • d with hDdef
  have hDd1 : d1 A u d ell j = D := rfl
  have hD : ∀ i, 0 < D i := fun i => by
    simp only [hDdef, Pi.smul_apply, smul_eq_mul]; have := hd i; positivity
  have hfD : f A u D e1 = 1 := by
    rw [hDdef, f_smul A u d e1 hc1, ← hf1def]; field_simp
  -- q₁ = f₁ q
  set q1 := col A j ⬝ᵥ ((B A D)⁻¹ *ᵥ col A j) with hq1
  have hq1eq : q1 = f1 * q := by
    rw [hq1, hDdef, B_smul, inv_smul_any _ hc1, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul, ← hq]
    field_simp
  have hq1pos : 0 < q1 := q_pos A hA D hD j
  set γ1 := slabRadius A u D e1 j with hγ1
  have hγ12 : γ1 ^ 2 = q1 := by rw [hγ1, slab_sq A hA u D e1 hD (by rw [hfD]; norm_num), hfD, one_mul]
  -- T = t_j(D, ℓ⁽¹⁾) = v_j(ℓ⁽¹⁾)
  have hyj : col A j ⬝ᵥ y A u D e1 = u j := by
    rw [hDdef, y_smul A u d e1 hc1, he1, y_shift, dotProduct_add, dotProduct_smul, smul_eq_mul,
      ← hq, hβ1, hγ2]
    field_simp
    rw [hδ]; ring
  have hT : t A u D e1 j = v u e1 j := by
    simp only [t, Pi.sub_apply, AT_mulVec_apply, hyj, v, r, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul]
    ring
  set V := v u e1 j with hV
  -- the d-update
  have hγ1pos : 0 < γ1 := by
    rw [hγ1]; exact slab_pos A u D e1 hA hD (by rw [hfD]; norm_num) j
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  set c := (2 / ((m : ℝ) - 1)) * (1 / γ1 ^ 2) with hc
  have hcpos : 0 < c := by
    rw [hc]; apply mul_pos (div_pos (by norm_num) (by linarith)); rw [hγ12]; positivity
  have hd2 : d2 A u d ell j = D + c • Pi.single j 1 := rfl
  have hcq : c * q1 = 2 / ((m : ℝ) - 1) := by
    rw [hc, ← hγ12]; field_simp
  -- f(d⁽²⁾, ℓ⁽¹⁾), t_j(d⁽²⁾,ℓ⁽¹⁾), q₂
  have hfd2 : f A u (D + c • Pi.single j 1) e1 = 1 + c * V ^ 2 - c / (1 + c * q1) * V ^ 2 := by
    rw [f_dshift A hA u D e1 hD j hcpos.le, hfD, ← hq1, hT]
  have htd2 : t A u (D + c • Pi.single j 1) e1 j = V - c / (1 + c * q1) * V * q1 := by
    rw [t_dshift A hA u D e1 hD j hcpos.le]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, AT_mulVec_apply]
    rw [← hq1, hT]
  have hqd2 := q_dshift A hA D hD j hcpos.le
  rw [← hq1] at hqd2
  have hD2pos := pos_dshift hD j hcpos.le
  -- the ℓ-update
  set β2 := 2 * (2 * V - γ1) / (((m : ℝ) - 1) * D j * γ1 ^ 2 + 2) with hβ2
  have hell2 : ell2 A u d ell j = e1 + β2 • Pi.single j 1 := rfl
  have hF2 : f A u (d2 A u d ell j) (ell2 A u d ell j) = (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1) := by
    rw [hd2, hell2, f_shift A hA u _ e1 hD2pos j β2, hfd2, htd2, hqd2, ← hV]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact alg61 m V γ1 (D j) c β2 q1 hm' hγ1pos (hD j) hγ12 hc hβ2
  refine ⟨((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2 / f1, ?_, ?_⟩
  · have hm2 : 0 < ((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2 := by
      apply div_pos (by nlinarith) (by positivity)
    rw [lt_div_iff₀ hf1]
    nlinarith
  · have hd3 : d3 A u d ell j = (1 / f A u (d2 A u d ell j) (ell2 A u d ell j)) • d2 A u d ell j := rfl
    rw [hd3, hF2, hd2]
    have hγpos : 0 < γ := by rw [hγ]; exact slab_pos A u d ell hA hd (by rw [hf]; norm_num) j
    have h4 : (2 : ℝ) * 2 ≤ (m : ℝ) * (m : ℝ) := mul_le_mul hm' hm' (by norm_num) (by linarith)
    have hm2 : (m : ℝ) ^ 2 - 1 ≠ 0 := ne_of_gt (by rw [sq]; linarith)
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hcoef : c = ((2 / ((m : ℝ) - 1)) * (1 / γ ^ 2)) / f1 := by
      rw [hc, hγ12, hq1eq, ← hγ2]; field_simp
    have hscal : 1 / ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) = ((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2 := by
      field_simp
    rw [hscal, hcoef, hDdef]
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp

end OEAThm61
end OblivEllipsoid.Infeas

open OblivEllipsoid.Infeas in
theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (j : Fin m)
    (hviol : 0 < OblivEllipsoid.Infeas.col A j ⬝ᵥ y A u d ell - u j)
    (hle : OblivEllipsoid.Infeas.col A j ⬝ᵥ y A u d ell - u j ≤ slabRadius A u d ell j)
    (hf1 : 0 < f A u d (ell1 A u d ell j)) :
    ∃ alpha : ℝ, (((m : ℝ) ^ 2 - 1) / (m : ℝ) ^ 2) < alpha ∧
      d3 A u d ell j = alpha •
        (d + ((2 / ((m : ℝ) - 1)) *
          (1 / slabRadius A u d ell j ^ 2)) • Pi.single j 1) :=
  OblivEllipsoid.Infeas.OEAThm61.thm61 A u d ell Lam hA hd hcert hf j hviol hle hf1
