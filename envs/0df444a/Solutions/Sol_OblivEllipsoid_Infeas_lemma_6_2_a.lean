-- Prove2me | solution 1 for OblivEllipsoid.Infeas.lemma_6_2_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:46:42.887394+00:00
-- url     : https://prove2.me/submissions/3f90d577-53fe-4dd3-bb9a-4b476ea2d8d6

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas
namespace OEALem62a

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

theorem lem62a (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (j : Fin m)
    (hviol : 0 < col A j ⬝ᵥ y A u d ell - u j)
    (hle : col A j ⬝ᵥ y A u d ell - u j ≤ slabRadius A u d ell j)
    (hf1 : 0 < f A u d (ell1 A u d ell j)) :
    ell2 A u d ell j j ≤ max (ell j) (Lb A u d ell j) := by
  set q := col A j ⬝ᵥ ((B A d)⁻¹ *ᵥ col A j) with hq
  have hqpos : 0 < q := q_pos A hA d hd j
  set γ := slabRadius A u d ell j with hγ
  have hγ2 : γ ^ 2 = q := by rw [hγ, slab_sq A hA u d ell hd (by rw [hf]; norm_num), hf, one_mul]
  have hγ0 : 0 ≤ γ := Real.sqrt_nonneg _
  set δ := col A j ⬝ᵥ y A u d ell - u j with hδ
  have hdj := hd j
  set β1 := -(2 * δ / (d j * γ ^ 2)) with hβ1
  have he1 : ell1 A u d ell j = ell + β1 • Pi.single j 1 := ell1_eq A u d ell j
  set e1 := ell1 A u d ell j with he1def
  -- f(d, ℓ⁽¹⁾) = 1 - δ²/q
  have hf1eq : f A u d e1 = 1 - δ ^ 2 / q := by
    rw [he1, f_shift A hA u d ell hd j β1, hf, t_sub_v, ← hδ, ← hq, hβ1, hγ2]
    field_simp
    ring
  set f1 := f A u d e1 with hf1def
  -- the new slab radius
  have hc1 : (1 / f1) ≠ 0 := by positivity
  set γ1 := slabRadius A u ((1 / f1) • d) e1 j with hγ1
  have hγ1eq : γ1 = Real.sqrt (q - δ ^ 2) := by
    rw [hγ1, slab_smul A u d e1 hc1 j]
    have h := slab_sq A hA u d e1 hd hf1.le j
    rw [← hf1def, ← hq, hf1eq] at h
    have h' : (1 - δ ^ 2 / q) * q = q - δ ^ 2 := by field_simp
    rw [h'] at h
    rw [← h]; exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
  have he1j : e1 j ≤ ell j := by
    rw [he1]; simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    have : 0 ≤ 2 * δ / (d j * γ ^ 2) := by positivity
    rw [hβ1]; linarith
  -- the second update
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast j.pos
  have hd1 : 0 < ((1 / f1) • d) j := by simp only [Pi.smul_apply, smul_eq_mul]; positivity
  set D := ((m : ℝ) - 1) * ((1 / f1) • d) j * γ1 ^ 2 + 2 with hD
  have hD2 : 2 ≤ D := by
    have : 0 ≤ ((m : ℝ) - 1) * ((1 / f1) • d) j * γ1 ^ 2 := by
      apply mul_nonneg (mul_nonneg (by linarith) hd1.le) (sq_nonneg _)
    linarith
  set N := 2 * v u e1 j - γ1 with hN
  have hell2 : ell2 A u d ell j j = e1 j + 2 * N / D := by
    simp only [ell2, d1, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    rfl
  rw [hell2]
  rcases le_or_gt N 0 with hN0 | hN0
  · have : 2 * N / D ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    exact le_max_of_le_left (by linarith)
  · have hβ2 : 2 * N / D ≤ N := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hv : 2 * v u e1 j = u j - e1 j := by
      simp only [v, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    -- γ - δ ≤ γ1
    have hkey : γ - δ ≤ γ1 := by
      rw [hγ1eq]
      apply Real.le_sqrt_of_sq_le
      nlinarith
    apply le_max_of_le_right
    simp only [Lb]
    rw [← hγ]
    have : e1 j + 2 * N / D ≤ u j - γ1 := by rw [hN] at hβ2 ⊢; linarith
    linarith

end OEALem62a
end OblivEllipsoid.Infeas

open OblivEllipsoid.Infeas in
theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (j : Fin m)
    (hviol : 0 < OblivEllipsoid.Infeas.col A j ⬝ᵥ y A u d ell - u j)
    (hle : OblivEllipsoid.Infeas.col A j ⬝ᵥ y A u d ell - u j ≤ slabRadius A u d ell j)
    (hf1 : 0 < f A u d (ell1 A u d ell j)) :
    ell2 A u d ell j j ≤ max (ell j) (Lb A u d ell j) :=
  OblivEllipsoid.Infeas.OEALem62a.lem62a A u d ell Lam hA hd hcert hf j hviol hle hf1
