-- Prove2me | solution 1 for OblivEllipsoid.Infeas.proposition_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:43:38.575464+00:00
-- url     : https://prove2.me/submissions/5f834af8-d108-4fa3-b1ab-53f7ea5015bc

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas
namespace OEAProp51

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

/-- The per-coordinate inequality (53)-(54) of Appendix E.1. -/
lemma coord_ineq (γ dj p rj lj uj vj : ℝ) (hγ : 0 ≤ γ) (hd : 0 ≤ dj)
    (hl : lj = rj - vj) (hu : uj = rj + vj) :
    max (γ * dj * p) 0 * uj - max (-(γ * dj * p)) 0 * lj ≤
      γ * dj * (p + rj) * p - γ / 2 * dj * ((p + rj - lj) * (p + rj - uj)) := by
  subst hl hu
  have h1 : 0 ≤ γ * dj * (p - vj) ^ 2 := by positivity
  have h2 : 0 ≤ γ * dj * (p + vj) ^ 2 := by positivity
  rcases le_total 0 (γ * dj * p) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_right h, max_eq_left (by linarith)]
    nlinarith

theorem prop51 (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (i : Fin m) :
    CertLBi A u i (Lb A u d ell i) (lamTilde A u d ell Lam i) := by
  obtain ⟨hAL, hL0, hLu⟩ := hcert
  have hBu := B_isUnit A hA d hd
  have hBinv : B A d * (B A d)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hBu)
  set w := (B A d)⁻¹ *ᵥ col A i with hw
  have hBw : B A d *ᵥ w = col A i := by
    rw [hw, Matrix.mulVec_mulVec, hBinv, Matrix.one_mulVec]
  set yy := y A u d ell with hyy
  have hBy : B A d *ᵥ yy = A *ᵥ (d * r u ell) := by
    rw [hyy, y, Matrix.mulVec_mulVec, hBinv, Matrix.one_mulVec]
  set tt := t A u d ell with htt
  have htt' : tt = Aᵀ *ᵥ yy - r u ell := rfl
  -- (I1) A D t = 0
  have hI1 : A *ᵥ (d * tt) = 0 := by
    rw [htt', mul_sub, Matrix.mulVec_sub, ← B_mulVec, hBy, sub_self]
  -- (I2) A D Aᵀ w = a_i
  have hI2 : A *ᵥ (d * (Aᵀ *ᵥ w)) = col A i := by rw [← B_mulVec, hBw]
  set q := col A i ⬝ᵥ w with hq
  have hγ : slabRadius A u d ell i = Real.sqrt q := by
    simp only [slabRadius, hf, one_mul]; rfl
  set γ := slabRadius A u d ell i with hγdef
  have hγpos : 0 < γ := slab_pos A u d ell hA hd (by rw [hf]; norm_num) i
  have hq0 : 0 ≤ q := by
    rw [hq, ← hBw, dotProduct_comm, quad_B]
    exact Finset.sum_nonneg fun k _ => by have := hd k; positivity
  have hγ2 : γ ^ 2 = q := by rw [hγ, Real.sq_sqrt hq0]
  -- λ̂
  set lh := lamHat A u d ell i with hlh
  have hlh' : lh = γ • (d * tt) - d * (Aᵀ *ᵥ w) := rfl
  have hAlh : A *ᵥ lh = -(col A i) := by
    rw [hlh', Matrix.mulVec_sub, Matrix.mulVec_smul, hI1, hI2, smul_zero, zero_sub]
  -- (1) A λ̃ = -a_i
  have hpn : posPart lh - negPart lh = lh := by
    funext k; simp only [posPart, negPart, Pi.sub_apply]
    rcases le_total 0 (lh k) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hAlt : A *ᵥ lamTilde A u d ell Lam i = -(col A i) := by
    simp only [lamTilde]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hAL, Matrix.neg_mulVec, ← sub_eq_neg_add,
      ← Matrix.mulVec_sub, ← hlh, hpn, hAlh]
  refine ⟨hAlt, ?_, ?_⟩
  · -- (2) nonnegativity
    intro k
    simp only [lamTilde, Pi.add_apply, Pi.zero_apply]
    have h1 : 0 ≤ (Lam *ᵥ negPart lh) k := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hL0 k j) (le_max_right _ _)
    have h2 : 0 ≤ posPart lh k := le_max_right _ _
    linarith
  · -- (3) -λ̃ᵀu ≥ L_i
    -- the point z on the boundary of E(d,ℓ)
    set c := 1 / γ with hc
    set p : Fin m → ℝ := fun j => tt j - c * (Aᵀ *ᵥ w) j with hp
    have hlhj : ∀ j, lh j = γ * d j * p j := by
      intro j
      simp only [hlh', hp, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hc]
      field_simp
    have hrv : ∀ j, ell j = r u ell j - v u ell j := by
      intro j; simp only [r, v, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]; ring
    have hru : ∀ j, u j = r u ell j + v u ell j := by
      intro j; simp only [r, v, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]; ring
    -- per coordinate
    have hcoord : ∀ j, posPart lh j * u j - negPart lh j * ell j ≤
        γ * d j * (p j + r u ell j) * p j -
          γ / 2 * d j * ((p j + r u ell j - ell j) * (p j + r u ell j - u j)) := by
      intro j
      simp only [posPart, negPart, hlhj]
      exact coord_ineq γ (d j) (p j) (r u ell j) (ell j) (u j) (v u ell j) hγpos.le (hd j).le
        (hrv j) (hru j)
    -- sums
    have hS1 : ∑ j, d j * tt j * (Aᵀ *ᵥ w) j = 0 := by
      have := dot_AT A (d * tt) w
      rw [hI1, zero_dotProduct] at this
      rw [← this]; simp [dotProduct]
    have hS2 : ∑ j, d j * (Aᵀ *ᵥ w) j * (Aᵀ *ᵥ w) j = q := by
      have := dot_AT A (d * (Aᵀ *ᵥ w)) w
      rw [hI2] at this
      rw [hq, ← this]; simp [dotProduct]
    have hS3 : ∑ j, d j * tt j * tt j - ∑ j, d j * v u ell j * v u ell j = -1 := by
      have : f A u d ell = ∑ j, d j * v u ell j ^ 2 - ∑ j, d j * tt j ^ 2 := rfl
      rw [hf] at this
      have e1 : ∑ j, d j * tt j * tt j = ∑ j, d j * tt j ^ 2 :=
        Finset.sum_congr rfl fun j _ => by ring
      have e2 : ∑ j, d j * v u ell j * v u ell j = ∑ j, d j * v u ell j ^ 2 :=
        Finset.sum_congr rfl fun j _ => by ring
      rw [e1, e2]; linarith
    -- (I4): the quadratic form vanishes at z
    have hQ : ∑ j, d j * ((p j + r u ell j - ell j) * (p j + r u ell j - u j)) = 0 := by
      have e : ∀ j, d j * ((p j + r u ell j - ell j) * (p j + r u ell j - u j)) =
          (d j * tt j * tt j - d j * v u ell j * v u ell j) - 2 * c * (d j * tt j * (Aᵀ *ᵥ w) j)
            + c ^ 2 * (d j * (Aᵀ *ᵥ w) j * (Aᵀ *ᵥ w) j) := by
        intro j; rw [hrv j, hru j]; simp only [hp]; ring
      rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hS1, hS2, hS3, hc]
      field_simp
      linarith [hγ2]
    -- (55): the sum of μ_j
    have hmu : ∑ j, γ * d j * (p j + r u ell j) * p j = γ - col A i ⬝ᵥ yy := by
      have e : ∀ j, γ * d j * (p j + r u ell j) * p j =
          lh j * ((Aᵀ *ᵥ yy) j - c * (Aᵀ *ᵥ w) j) := by
        intro j
        rw [hlhj]; simp only [hp, htt', Pi.sub_apply]; ring
      rw [Finset.sum_congr rfl fun j _ => e j]
      have : ∑ j, lh j * ((Aᵀ *ᵥ yy) j - c * (Aᵀ *ᵥ w) j) = lh ⬝ᵥ (Aᵀ *ᵥ (yy - c • w)) := by
        simp only [dotProduct, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul]
      rw [this, dot_AT, hAlh, neg_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hq,
        hc]
      have : 1 / γ * q = γ := by rw [← hγ2]; field_simp
      rw [this]; ring
    have hsum : ∑ j, (posPart lh j * u j - negPart lh j * ell j) ≤ γ - col A i ⬝ᵥ yy := by
      calc ∑ j, (posPart lh j * u j - negPart lh j * ell j)
          ≤ ∑ j, (γ * d j * (p j + r u ell j) * p j -
              γ / 2 * d j * ((p j + r u ell j - ell j) * (p j + r u ell j - u j))) :=
            Finset.sum_le_sum fun j _ => hcoord j
        _ = ∑ j, γ * d j * (p j + r u ell j) * p j -
              γ / 2 * ∑ j, d j * ((p j + r u ell j - ell j) * (p j + r u ell j - u j)) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
            congr 1; refine Finset.sum_congr rfl fun j _ => by ring
        _ = γ - col A i ⬝ᵥ yy := by rw [hQ, hmu]; ring
    -- negative part against the certified bounds
    have hneg : negPart lh ⬝ᵥ ell ≤ -((Lam *ᵥ negPart lh) ⬝ᵥ u) := by
      have : (Lam *ᵥ negPart lh) ⬝ᵥ u = negPart lh ⬝ᵥ (Lamᵀ *ᵥ u) := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
      rw [this, ← dotProduct_neg]
      simp only [dotProduct]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hLu j) (le_max_right _ _)
    simp only [Lb, lamTilde, add_dotProduct, neg_add]
    have e : ∑ j, (posPart lh j * u j - negPart lh j * ell j) =
        posPart lh ⬝ᵥ u - negPart lh ⬝ᵥ ell := by
      simp [dotProduct, Finset.sum_sub_distrib]
    rw [e] at hsum
    rw [← hγdef, ← hyy]
    linarith

end OEAProp51
end OblivEllipsoid.Infeas

open OblivEllipsoid.Infeas in
theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (i : Fin m) :
    CertLBi A u i (Lb A u d ell i) (lamTilde A u d ell Lam i) :=
  OblivEllipsoid.Infeas.OEAProp51.prop51 A u d ell Lam hA hd hcert hf i
