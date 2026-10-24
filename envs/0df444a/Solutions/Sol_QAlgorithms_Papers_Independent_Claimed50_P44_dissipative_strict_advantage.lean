-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P44.dissipative_strict_advantage
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T23:28:02.861622+00:00
-- url     : https://prove2.me/submissions/f04a78b6-9835-41de-96be-43726ab0a441

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Matrix ComplexOrder

namespace P44Aux

open QAlgorithms.Papers.Independent.Claimed50.P44
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)


open MeasureTheory

theorem gauss1 {A : ℝ} (hA : 0 < A) (L k : ℝ) :
    ∫ x : ℝ, Real.exp (-(A * x ^ 2 + L * x + k)) =
      Real.sqrt (Real.pi / A) * Real.exp (L ^ 2 / (4 * A) - k) := by
  have h : ∀ x : ℝ, Real.exp (-(A * x ^ 2 + L * x + k)) =
      Real.exp (L ^ 2 / (4 * A) - k) * Real.exp (-A * (x + L / (2 * A)) ^ 2) := by
    intro x
    rw [← Real.exp_add]; congr 1; field_simp; ring
  simp_rw [h]
  rw [integral_const_mul]
  have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun x => Real.exp (-A * x ^ 2)) (L / (2 * A))
  rw [this, integral_gaussian]
  ring

theorem gi2 {A B C : ℝ} (hC : 0 < C) (hD : 0 < A * C - B ^ 2) (L0 L1 k : ℝ) :
    ∫ x : ℝ, ∫ p : ℝ, Real.exp (-(A * x ^ 2 + 2 * B * x * p + C * p ^ 2 + L0 * x + L1 * p + k)) =
      Real.pi / Real.sqrt (A * C - B ^ 2) *
        Real.exp ((C * L0 ^ 2 - 2 * B * L0 * L1 + A * L1 ^ 2) / (4 * (A * C - B ^ 2)) - k) := by
  have hin : ∀ x : ℝ, ∫ p : ℝ, Real.exp (-(A * x ^ 2 + 2 * B * x * p + C * p ^ 2 + L0 * x + L1 * p + k)) =
      Real.sqrt (Real.pi / C) * Real.exp (-(((A * C - B ^ 2) / C) * x ^ 2 + (L0 - B * L1 / C) * x +
        (k - L1 ^ 2 / (4 * C)))) := by
    intro x
    have h1 : ∀ p : ℝ, (A * x ^ 2 + 2 * B * x * p + C * p ^ 2 + L0 * x + L1 * p + k) =
        C * p ^ 2 + (2 * B * x + L1) * p + (A * x ^ 2 + L0 * x + k) := fun p => by ring
    simp_rw [h1]
    rw [gauss1 hC]
    congr 2
    field_simp
    ring
  simp_rw [hin]
  rw [integral_const_mul, gauss1 (div_pos hD hC)]
  have hs : Real.sqrt (Real.pi / C) * Real.sqrt (Real.pi / ((A * C - B ^ 2) / C)) =
      Real.pi / Real.sqrt (A * C - B ^ 2) := by
    rw [← Real.sqrt_mul (div_nonneg Real.pi_pos.le hC.le)]
    rw [show Real.pi / C * (Real.pi / ((A * C - B ^ 2) / C)) = Real.pi ^ 2 / (A * C - B ^ 2) by
      field_simp]
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq Real.pi_pos.le]
  rw [← mul_assoc, hs]
  congr 2
  obtain ⟨X, hX⟩ : ∃ X, X = A * C - B ^ 2 := ⟨_, rfl⟩
  rw [← hX]
  have hXne : X ≠ 0 := by rw [hX]; exact hD.ne'
  have hCne : C ≠ 0 := hC.ne'
  field_simp
  rw [hX]
  ring

/-- Isotropic Gaussian density of N(0, beta I / 2). -/
def GI (β x y : ℝ) : ℝ := Real.exp (-((x ^ 2 + y ^ 2) / β)) / (Real.pi * β)

/-- General 2D Gaussian density of N(0, Sigma / 2), Sigma = [[s11,s12],[s12,s22]]. -/
def G2 (s11 s12 s22 x y : ℝ) : ℝ :=
  Real.exp (-((s22 * x ^ 2 - 2 * s12 * x * y + s11 * y ^ 2) / (s11 * s22 - s12 ^ 2))) /
    (Real.pi * Real.sqrt (s11 * s22 - s12 ^ 2))

theorem pdform_nonneg {s11 s12 s22 : ℝ} (hs : 0 < s11) (hD : 0 < s11 * s22 - s12 ^ 2) (x y : ℝ) :
    0 ≤ s22 * x ^ 2 - 2 * s12 * x * y + s11 * y ^ 2 := by
  have h : s11 * (s22 * x ^ 2 - 2 * s12 * x * y + s11 * y ^ 2) =
      (s11 * y - s12 * x) ^ 2 + (s11 * s22 - s12 ^ 2) * x ^ 2 := by ring
  have : 0 ≤ s11 * (s22 * x ^ 2 - 2 * s12 * x * y + s11 * y ^ 2) := by
    rw [h]; positivity
  exact (mul_nonneg_iff_of_pos_left hs).mp this

theorem conv2 {β s11 s12 s22 : ℝ} (hβ : 0 < β) (hs : 0 < s11) (hD : 0 < s11 * s22 - s12 ^ 2)
    (k00 k01 k10 k11 y0 y1 : ℝ) :
    ∫ v0 : ℝ, ∫ v1 : ℝ, GI β v0 v1 *
        G2 s11 s12 s22 (y0 + k00 * v0 + k01 * v1) (y1 + k10 * v0 + k11 * v1) =
      G2 (s11 + β * (k00 ^ 2 + k01 ^ 2)) (s12 + β * (k00 * k10 + k01 * k11))
        (s22 + β * (k10 ^ 2 + k11 ^ 2)) y0 y1 := by
  have hDne : s11 * s22 - s12 ^ 2 ≠ 0 := hD.ne'
  have hβne : β ≠ 0 := hβ.ne'
  have hq := pdform_nonneg hs hD
  have hpt : ∀ v0 v1 : ℝ, GI β v0 v1 *
      G2 s11 s12 s22 (y0 + k00 * v0 + k01 * v1) (y1 + k10 * v0 + k11 * v1) =
      (1 / (Real.pi * β) / (Real.pi * Real.sqrt (s11 * s22 - s12 ^ 2))) *
        Real.exp (-((1 / β + (s22 * k00 ^ 2 - 2 * s12 * k00 * k10 + s11 * k10 ^ 2) / (s11 * s22 - s12 ^ 2)) * v0 ^ 2 +
          2 * ((s22 * k00 * k01 - s12 * (k00 * k11 + k01 * k10) + s11 * k10 * k11) / (s11 * s22 - s12 ^ 2)) * v0 * v1 +
          (1 / β + (s22 * k01 ^ 2 - 2 * s12 * k01 * k11 + s11 * k11 ^ 2) / (s11 * s22 - s12 ^ 2)) * v1 ^ 2 +
          (2 * (s22 * y0 * k00 - s12 * (y0 * k10 + y1 * k00) + s11 * y1 * k10) / (s11 * s22 - s12 ^ 2)) * v0 +
          (2 * (s22 * y0 * k01 - s12 * (y0 * k11 + y1 * k01) + s11 * y1 * k11) / (s11 * s22 - s12 ^ 2)) * v1 +
          (s22 * y0 ^ 2 - 2 * s12 * y0 * y1 + s11 * y1 ^ 2) / (s11 * s22 - s12 ^ 2))) := by
    intro v0 v1
    simp only [GI, G2]
    rw [div_mul_div_comm, ← Real.exp_add]
    have key : ∀ X Y a b : ℝ, X = Y → Real.exp X / (a * b) = 1 / a / b * Real.exp Y := by
      intro X Y a b h; rw [h]; ring
    apply key
    ring
  simp_rw [hpt]
  simp_rw [integral_const_mul]
  set D := s11 * s22 - s12 ^ 2 with hDdef
  set A := 1 / β + (s22 * k00 ^ 2 - 2 * s12 * k00 * k10 + s11 * k10 ^ 2) / D with hA
  set B := (s22 * k00 * k01 - s12 * (k00 * k11 + k01 * k10) + s11 * k10 * k11) / D with hB
  set C := 1 / β + (s22 * k01 ^ 2 - 2 * s12 * k01 * k11 + s11 * k11 ^ 2) / D with hC
  set L0 := 2 * (s22 * y0 * k00 - s12 * (y0 * k10 + y1 * k00) + s11 * y1 * k10) / D with hL0
  set L1 := 2 * (s22 * y0 * k01 - s12 * (y0 * k11 + y1 * k01) + s11 * y1 * k11) / D with hL1
  set k := (s22 * y0 ^ 2 - 2 * s12 * y0 * y1 + s11 * y1 ^ 2) / D with hk
  set D' := (s11 + β * (k00 ^ 2 + k01 ^ 2)) * (s22 + β * (k10 ^ 2 + k11 ^ 2)) -
    (s12 + β * (k00 * k10 + k01 * k11)) ^ 2 with hD'
  have hD'eq : D' = D + β * ((s22 * k00 ^ 2 - 2 * s12 * k00 * k10 + s11 * k10 ^ 2) +
      (s22 * k01 ^ 2 - 2 * s12 * k01 * k11 + s11 * k11 ^ 2)) + β ^ 2 * (k00 * k11 - k01 * k10) ^ 2 := by
    rw [hD', hDdef]; ring
  have hD'pos : 0 < D' := by
    rw [hD'eq]
    have h1 := hq k00 k10
    have h2 := hq k01 k11
    positivity
  have hCpos : 0 < C := by
    rw [hC]; have := hq k01 k11; positivity
  have hD'ne : D' ≠ 0 := hD'pos.ne'
  have hX : A * C - B ^ 2 = D' / (β ^ 2 * D) := by
    rw [hA, hB, hC]; field_simp; rw [hD'eq, hDdef]; ring
  have hXpos : 0 < A * C - B ^ 2 := by rw [hX]; positivity
  rw [gi2 hCpos hXpos]
  have hE : (C * L0 ^ 2 - 2 * B * L0 * L1 + A * L1 ^ 2) / (4 * (A * C - B ^ 2)) - k =
      -(((s22 + β * (k10 ^ 2 + k11 ^ 2)) * y0 ^ 2 - 2 * (s12 + β * (k00 * k10 + k01 * k11)) * y0 * y1 +
        (s11 + β * (k00 ^ 2 + k01 ^ 2)) * y1 ^ 2) / D') := by
    rw [hX, hA, hB, hC, hL0, hL1, hk]
    field_simp
    rw [hD'eq, hDdef]
    ring
  rw [hE, hX]
  simp only [G2]
  rw [← hD']
  have hsq : Real.sqrt (D' / (β ^ 2 * D)) = Real.sqrt D' / (β * Real.sqrt D) := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ.le]
  rw [hsq]
  have h1 : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have h2 : 0 < Real.sqrt D' := Real.sqrt_pos.mpr hD'pos
  field_simp

theorem det_resourceCov {α : ℝ} (hα : α ≠ 0) (B K : QuadratureMatrix) (hB : B 1 0 = B 0 1) :
    (resourceCov (α • (1 : QuadratureMatrix)) B K).det =
      α ^ 2 * ((B 0 0 - (K 0 0 ^ 2 + K 1 0 ^ 2) / α) * (B 1 1 - (K 0 1 ^ 2 + K 1 1 ^ 2) / α) -
        (B 0 1 - (K 0 0 * K 0 1 + K 1 0 * K 1 1) / α) ^ 2) := by
  have hinv : (α • (1 : QuadratureMatrix)) * (α⁻¹ • 1) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hα, one_smul]
  haveI : Invertible (α • (1 : QuadratureMatrix)) :=
    Matrix.invertibleOfIsUnitDet _ (by
      rw [isUnit_iff_ne_zero, Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ hα)
  unfold resourceCov
  rw [Matrix.det_fromBlocks₁₁, invOf_eq_right_inv hinv]
  simp [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hB, -mul_eq_mul_left_iff,
    -mul_eq_mul_right_iff]
  field_simp
  try ring

/-- Explicit inverse of resourceCov (alpha 1) B K via the Schur complement. -/
def Minv (α s11 s12 s22 Dc : ℝ) (K : QuadratureMatrix) : JointMat :=
  Matrix.fromBlocks
    (α⁻¹ • 1 + (α⁻¹ ^ 2) • (K * !![s22 / Dc, -s12 / Dc; -s12 / Dc, s11 / Dc] * Kᵀ))
    ((-α⁻¹) • (K * !![s22 / Dc, -s12 / Dc; -s12 / Dc, s11 / Dc]))
    ((-α⁻¹) • (!![s22 / Dc, -s12 / Dc; -s12 / Dc, s11 / Dc] * Kᵀ))
    !![s22 / Dc, -s12 / Dc; -s12 / Dc, s11 / Dc]

set_option maxRecDepth 8000 in
theorem fact4 {α : ℝ} (hα : 0 < α) (B K : QuadratureMatrix) (hB : B 1 0 = B 0 1)
    (hs : 0 < B 0 0 - (K 0 0 ^ 2 + K 1 0 ^ 2) / α)
    (hD : 0 < (B 0 0 - (K 0 0 ^ 2 + K 1 0 ^ 2) / α) * (B 1 1 - (K 0 1 ^ 2 + K 1 1 ^ 2) / α) -
        (B 0 1 - (K 0 0 * K 0 1 + K 1 0 * K 1 1) / α) ^ 2)
    (d a b : PhasePoint) :
    resourceWigner (resourceCov (α • (1 : QuadratureMatrix)) B K) d a b =
      GI α (a 0) (a 1) *
        G2 (B 0 0 - (K 0 0 ^ 2 + K 1 0 ^ 2) / α) (B 0 1 - (K 0 0 * K 0 1 + K 1 0 * K 1 1) / α)
          (B 1 1 - (K 0 1 ^ 2 + K 1 1 ^ 2) / α)
          (b 0 - d 0 - (K 0 0 * a 0 + K 1 0 * a 1) / α) (b 1 - d 1 - (K 0 1 * a 0 + K 1 1 * a 1) / α) := by
  have hαne : α ≠ 0 := hα.ne'
  have hdet := det_resourceCov hαne B K hB
  obtain ⟨s11, h11⟩ : ∃ s, s = B 0 0 - (K 0 0 ^ 2 + K 1 0 ^ 2) / α := ⟨_, rfl⟩
  obtain ⟨s12, h12⟩ : ∃ s, s = B 0 1 - (K 0 0 * K 0 1 + K 1 0 * K 1 1) / α := ⟨_, rfl⟩
  obtain ⟨s22, h22⟩ : ∃ s, s = B 1 1 - (K 0 1 ^ 2 + K 1 1 ^ 2) / α := ⟨_, rfl⟩
  rw [← h11, ← h12, ← h22] at hD hdet ⊢
  rw [← h11] at hs
  obtain ⟨Dc, hDc⟩ : ∃ D, D = s11 * s22 - s12 ^ 2 := ⟨_, rfl⟩
  rw [← hDc] at hD hdet
  have hDcne : Dc ≠ 0 := hD.ne'
  have hB00 : B 0 0 = s11 + (K 0 0 ^ 2 + K 1 0 ^ 2) / α := by rw [h11]; ring
  have hB01 : B 0 1 = s12 + (K 0 0 * K 0 1 + K 1 0 * K 1 1) / α := by rw [h12]; ring
  have hB11 : B 1 1 = s22 + (K 0 1 ^ 2 + K 1 1 ^ 2) / α := by rw [h22]; ring
  have hVM : resourceCov (α • (1 : QuadratureMatrix)) B K * Minv α s11 s12 s22 Dc K = 1 := by
    rw [Minv, resourceCov, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, hB, hB00, hB01, hB11] <;> field_simp <;>
      (try rw [hDc]) <;> ring
  have hinv : (resourceCov (α • (1 : QuadratureMatrix)) B K)⁻¹ = Minv α s11 s12 s22 Dc K :=
    Matrix.inv_eq_right_inv hVM
  unfold resourceWigner gaussianWigner
  rw [hinv, hdet]
  have hcard : (Fintype.card PairMode / 2 : ℕ) = 2 := by simp
  rw [hcard]
  have hq : quadratic (Minv α s11 s12 s22 Dc K) (joinPhasePoints a b - joinPhasePoints 0 d) =
      (a 0 ^ 2 + a 1 ^ 2) / α +
        (s22 * (b 0 - d 0 - (K 0 0 * a 0 + K 1 0 * a 1) / α) ^ 2 -
          2 * s12 * (b 0 - d 0 - (K 0 0 * a 0 + K 1 0 * a 1) / α) *
            (b 1 - d 1 - (K 0 1 * a 0 + K 1 1 * a 1) / α) +
          s11 * (b 1 - d 1 - (K 0 1 * a 0 + K 1 1 * a 1) / α) ^ 2) / Dc := by
    simp [quadratic, Minv, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, joinPhasePoints]
    field_simp
    ring
  rw [hq]
  have hsq : Real.sqrt (α ^ 2 * Dc) = α * Real.sqrt Dc := by
    rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]
  rw [hsq]
  simp only [GI, G2]
  rw [← hDc]
  rw [div_mul_div_comm, ← Real.exp_add, neg_add]
  congr 1
  ring


theorem pd_update {β s11 s12 s22 : ℝ} (hβ : 0 ≤ β) (hs : 0 < s11) (hD : 0 < s11 * s22 - s12 ^ 2)
    (k00 k01 k10 k11 : ℝ) :
    0 < s11 + β * (k00 ^ 2 + k01 ^ 2) ∧
    0 < (s11 + β * (k00 ^ 2 + k01 ^ 2)) * (s22 + β * (k10 ^ 2 + k11 ^ 2)) -
      (s12 + β * (k00 * k10 + k01 * k11)) ^ 2 := by
  have hq := pdform_nonneg hs hD
  refine ⟨by positivity, ?_⟩
  have h1 := hq k00 k10
  have h2 := hq k01 k11
  have e : (s11 + β * (k00 ^ 2 + k01 ^ 2)) * (s22 + β * (k10 ^ 2 + k11 ^ 2)) -
      (s12 + β * (k00 * k10 + k01 * k11)) ^ 2 = (s11 * s22 - s12 ^ 2) +
      β * ((s22 * k00 ^ 2 - 2 * s12 * k00 * k10 + s11 * k10 ^ 2) +
        (s22 * k01 ^ 2 - 2 * s12 * k01 * k11 + s11 * k11 ^ 2)) + β ^ 2 * (k00 * k11 - k01 * k10) ^ 2 := by
    ring
  rw [e]; positivity

theorem pi_translate (H : ℝ → ℝ → ℝ) (c0 c1 : ℝ) :
    ∫ v0 : ℝ, ∫ v1 : ℝ, H (v0 - c0) (v1 - c1) = ∫ u0 : ℝ, ∫ u1 : ℝ, H u0 u1 := by
  have h1 : ∀ v0 : ℝ, ∫ v1 : ℝ, H (v0 - c0) (v1 - c1) = ∫ u1 : ℝ, H (v0 - c0) u1 :=
    fun v0 => integral_sub_right_eq_self (fun u1 => H (v0 - c0) u1) c1
  simp_rw [h1]
  exact integral_sub_right_eq_self (fun u0 => ∫ u1 : ℝ, H u0 u1) c0

theorem conv2c {β s11 s12 s22 : ℝ} (hβ : 0 < β) (hs : 0 < s11) (hD : 0 < s11 * s22 - s12 ^ 2)
    (k00 k01 k10 k11 y0 y1 c0 c1 M : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : ∀ v0 v1, f v0 v1 = M * (GI β (v0 - c0) (v1 - c1) *
      G2 s11 s12 s22 (y0 + k00 * v0 + k01 * v1) (y1 + k10 * v0 + k11 * v1))) :
    ∫ v0 : ℝ, ∫ v1 : ℝ, f v0 v1 =
      M * G2 (s11 + β * (k00 ^ 2 + k01 ^ 2)) (s12 + β * (k00 * k10 + k01 * k11))
        (s22 + β * (k10 ^ 2 + k11 ^ 2)) (y0 + k00 * c0 + k01 * c1) (y1 + k10 * c0 + k11 * c1) := by
  have hf' : ∀ v0 v1, f v0 v1 = M * (GI β (v0 - c0) (v1 - c1) *
      G2 s11 s12 s22 ((y0 + k00 * c0 + k01 * c1) + k00 * (v0 - c0) + k01 * (v1 - c1))
        ((y1 + k10 * c0 + k11 * c1) + k10 * (v0 - c0) + k11 * (v1 - c1))) := by
    intro v0 v1
    rw [hf]
    rw [show (y0 + k00 * c0 + k01 * c1) + k00 * (v0 - c0) + k01 * (v1 - c1) =
        y0 + k00 * v0 + k01 * v1 by ring,
      show (y1 + k10 * c0 + k11 * c1) + k10 * (v0 - c0) + k11 * (v1 - c1) =
        y1 + k10 * v0 + k11 * v1 by ring]
  simp_rw [hf', integral_const_mul]
  have ht := pi_translate (fun u0 u1 => GI β u0 u1 *
      G2 s11 s12 s22 ((y0 + k00 * c0 + k01 * c1) + k00 * u0 + k01 * u1)
        ((y1 + k10 * c0 + k11 * c1) + k10 * u0 + k11 * u1)) c0 c1
  beta_reduce at ht
  rw [ht, conv2 hβ hs hD]

theorem GI_swap (β x0 x1 y0 y1 : ℝ) : GI β (x0 - y0) (x1 - y1) = GI β (y0 - x0) (y1 - x1) := by
  unfold GI; ring_nf

theorem prodGI {α : ℝ} (hα : 0 < α) (w0 w1 m0 m1 c0 c1 : ℝ) :
    GI 1 (w0 - m0) (w1 - m1) * GI α (c0 - w0) (w1 - c1) =
      GI (1 + α) (m0 - c0) (m1 - c1) *
        GI (α / (1 + α)) (w0 - (α * m0 + c0) / (1 + α)) (w1 - (α * m1 + c1) / (1 + α)) := by
  have hα1 : (1 + α) ≠ 0 := by positivity
  have hαne : α ≠ 0 := hα.ne'
  unfold GI
  rw [div_mul_div_comm, div_mul_div_comm, ← Real.exp_add, ← Real.exp_add]
  congr 1
  · congr 1; field_simp; ring
  · field_simp; try ring

theorem in_eq (μ z : PhasePoint) :
    gaussianWigner (1 : QuadratureMatrix) μ z = GI 1 (z 0 - μ 0) (z 1 - μ 1) := by
  unfold gaussianWigner GI quadratic
  simp [Fin.sum_univ_two, Matrix.one_apply]
  ring_nf

theorem pi_scale (H f : ℝ → ℝ → ℝ)
    (hf : ∀ o0 o1, f o0 o1 = 2 * H (Real.sqrt 2 * o0) (Real.sqrt 2 * o1)) :
    ∫ o0 : ℝ, ∫ o1 : ℝ, f o0 o1 = ∫ s0 : ℝ, ∫ s1 : ℝ, H s0 s1 := by
  simp_rw [hf, integral_const_mul]
  have h1 : ∀ o0 : ℝ, ∫ o1 : ℝ, H (Real.sqrt 2 * o0) (Real.sqrt 2 * o1) =
      |(Real.sqrt 2)⁻¹| • ∫ s1 : ℝ, H (Real.sqrt 2 * o0) s1 :=
    fun o0 => Measure.integral_comp_mul_left (fun s1 => H (Real.sqrt 2 * o0) s1) (Real.sqrt 2)
  simp_rw [h1, smul_eq_mul, integral_const_mul]
  rw [Measure.integral_comp_mul_left (fun s0 => ∫ s1 : ℝ, H s0 s1) (Real.sqrt 2), smul_eq_mul]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := by positivity
  rw [abs_of_pos (inv_pos.mpr hpos)]
  rw [← mul_assoc, ← mul_assoc]
  have : 2 * (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 := by
    field_simp; linarith
  rw [this, one_mul]

theorem stepB {α : ℝ} (hα : 0 < α) (B K : QuadratureMatrix) (hB : B 1 0 = B 0 1)
    {s11 s12 s22 : ℝ} (h11 : s11 = B 0 0 - (K 0 0 ^ 2 + K 1 0 ^ 2) / α)
    (h12 : s12 = B 0 1 - (K 0 0 * K 0 1 + K 1 0 * K 1 1) / α)
    (h22 : s22 = B 1 1 - (K 0 1 ^ 2 + K 1 1 ^ 2) / α)
    (hs : 0 < s11) (hD : 0 < s11 * s22 - s12 ^ 2) (μ d o bob : PhasePoint) :
    bellBranch (gaussianWigner (1 : QuadratureMatrix) μ)
        (resourceWigner (resourceCov (α • (1 : QuadratureMatrix)) B K) d) o bob =
      2 * (GI (1 + α) (μ 0 - Real.sqrt 2 * o 0) (μ 1 - Real.sqrt 2 * o 1) *
        G2 (s11 + α / (1 + α) * ((K 0 0 / α) ^ 2 + (-(K 1 0) / α) ^ 2))
          (s12 + α / (1 + α) * ((K 0 0 / α) * (K 0 1 / α) + (-(K 1 0) / α) * (-(K 1 1) / α)))
          (s22 + α / (1 + α) * ((K 0 1 / α) ^ 2 + (-(K 1 1) / α) ^ 2))
          ((bob 0 - d 0 - (K 0 0 * (Real.sqrt 2 * o 0) - K 1 0 * (Real.sqrt 2 * o 1)) / α) +
            K 0 0 / α * ((α * μ 0 + Real.sqrt 2 * o 0) / (1 + α)) +
            -(K 1 0) / α * ((α * μ 1 + Real.sqrt 2 * o 1) / (1 + α)))
          ((bob 1 - d 1 - (K 0 1 * (Real.sqrt 2 * o 0) - K 1 1 * (Real.sqrt 2 * o 1)) / α) +
            K 0 1 / α * ((α * μ 0 + Real.sqrt 2 * o 0) / (1 + α)) +
            -(K 1 1) / α * ((α * μ 1 + Real.sqrt 2 * o 1) / (1 + α)))) := by
  have hf4 := fact4 hα B K hB (by rw [← h11]; exact hs) (by rw [← h11, ← h12, ← h22]; exact hD) d
  unfold bellBranch phaseIntegral
  congr 1
  apply conv2c (β := α / (1 + α)) (by positivity) hs hD (K 0 0 / α) (-(K 1 0) / α) (K 0 1 / α)
    (-(K 1 1) / α)
  intro w0 w1
  simp only [in_eq, hf4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [← h11, ← h12, ← h22, ← mul_assoc (GI 1 _ _), prodGI hα, mul_assoc (GI (1 + α) _ _)]
  congr 3 <;> ring

theorem stepO {α : ℝ} (hα : 0 < α) (B K : QuadratureMatrix) (hB : B 1 0 = B 0 1)
    {s11 s12 s22 : ℝ} (h11 : s11 = B 0 0 - (K 0 0 ^ 2 + K 1 0 ^ 2) / α)
    (h12 : s12 = B 0 1 - (K 0 0 * K 0 1 + K 1 0 * K 1 1) / α)
    (h22 : s22 = B 1 1 - (K 0 1 ^ 2 + K 1 1 ^ 2) / α)
    (hs : 0 < s11) (hD : 0 < s11 * s22 - s12 ^ 2)
    {t11 t12 t22 : ℝ} (ht11 : t11 = s11 + α / (1 + α) * ((K 0 0 / α) ^ 2 + (-(K 1 0) / α) ^ 2))
    (ht12 : t12 = s12 + α / (1 + α) * ((K 0 0 / α) * (K 0 1 / α) + (-(K 1 0) / α) * (-(K 1 1) / α)))
    (ht22 : t22 = s22 + α / (1 + α) * ((K 0 1 / α) ^ 2 + (-(K 1 1) / α) ^ 2))
    (μ d z : PhasePoint) :
    bellOutput (gaussianWigner (1 : QuadratureMatrix) μ)
        (resourceWigner (resourceCov (α • (1 : QuadratureMatrix)) B K) d) z =
      1 * G2 (t11 + (1 + α) * ((-1 - K 0 0 / (1 + α)) ^ 2 + (K 1 0 / (1 + α)) ^ 2))
        (t12 + (1 + α) * ((-1 - K 0 0 / (1 + α)) * (-(K 0 1) / (1 + α)) +
          (K 1 0 / (1 + α)) * (-1 + K 1 1 / (1 + α))))
        (t22 + (1 + α) * ((-(K 0 1) / (1 + α)) ^ 2 + (-1 + K 1 1 / (1 + α)) ^ 2))
        ((z 0 - d 0 + (K 0 0 * μ 0 - K 1 0 * μ 1) / (1 + α)) + (-1 - K 0 0 / (1 + α)) * μ 0 +
          K 1 0 / (1 + α) * μ 1)
        ((z 1 - d 1 + (K 0 1 * μ 0 - K 1 1 * μ 1) / (1 + α)) + -(K 0 1) / (1 + α) * μ 0 +
          (-1 + K 1 1 / (1 + α)) * μ 1) := by
  have hαne : α ≠ 0 := hα.ne'
  have hα1 : 1 + α ≠ 0 := by positivity
  have ht := pd_update (β := α / (1 + α)) (by positivity) hs hD (K 0 0 / α) (-(K 1 0) / α)
    (K 0 1 / α) (-(K 1 1) / α)
  rw [← ht11, ← ht12, ← ht22] at ht
  unfold bellOutput phaseIntegral
  simp_rw [stepB hα B K hB h11 h12 h22 hs hD]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [← ht11, ← ht12, ← ht22]
  rw [pi_scale (fun s0 s1 => GI (1 + α) (μ 0 - s0) (μ 1 - s1) *
      G2 t11 t12 t22
        ((z 0 - s0 - d 0 - (K 0 0 * s0 - K 1 0 * s1) / α) +
          K 0 0 / α * ((α * μ 0 + s0) / (1 + α)) + -(K 1 0) / α * ((α * μ 1 + s1) / (1 + α)))
        ((z 1 - s1 - d 1 - (K 0 1 * s0 - K 1 1 * s1) / α) +
          K 0 1 / α * ((α * μ 0 + s0) / (1 + α)) + -(K 1 1) / α * ((α * μ 1 + s1) / (1 + α))))
      _ (fun o0 o1 => rfl)]
  apply conv2c (β := 1 + α) (by positivity) ht.1 ht.2
  intro s0 s1
  rw [one_mul, GI_swap (1 + α) (μ 0) (μ 1) s0 s1]
  congr 2 <;> field_simp <;> ring

theorem MF {α : ℝ} (hα : 0 < α) (B K : QuadratureMatrix) (hB : B 1 0 = B 0 1)
    {s11 s12 s22 : ℝ} (h11 : s11 = B 0 0 - (K 0 0 ^ 2 + K 1 0 ^ 2) / α)
    (h12 : s12 = B 0 1 - (K 0 0 * K 0 1 + K 1 0 * K 1 1) / α)
    (h22 : s22 = B 1 1 - (K 0 1 ^ 2 + K 1 1 ^ 2) / α)
    (hs : 0 < s11) (hD : 0 < s11 * s22 - s12 ^ 2)
    {t11 t12 t22 : ℝ} (ht11 : t11 = s11 + α / (1 + α) * ((K 0 0 / α) ^ 2 + (-(K 1 0) / α) ^ 2))
    (ht12 : t12 = s12 + α / (1 + α) * ((K 0 0 / α) * (K 0 1 / α) + (-(K 1 0) / α) * (-(K 1 1) / α)))
    (ht22 : t22 = s22 + α / (1 + α) * ((K 0 1 / α) ^ 2 + (-(K 1 1) / α) ^ 2))
    {u11 u12 u22 : ℝ}
    (hu11 : u11 = t11 + (1 + α) * ((-1 - K 0 0 / (1 + α)) ^ 2 + (K 1 0 / (1 + α)) ^ 2))
    (hu12 : u12 = t12 + (1 + α) * ((-1 - K 0 0 / (1 + α)) * (-(K 0 1) / (1 + α)) +
          (K 1 0 / (1 + α)) * (-1 + K 1 1 / (1 + α))))
    (hu22 : u22 = t22 + (1 + α) * ((-(K 0 1) / (1 + α)) ^ 2 + (-1 + K 1 1 / (1 + α)) ^ 2))
    (μ d : PhasePoint) :
    bellAverageFidelity 1 μ (resourceWigner (resourceCov (α • (1 : QuadratureMatrix)) B K) d) =
      2 * Real.pi * (1 * G2 (u11 + 1 * (1 ^ 2 + 0 ^ 2)) (u12 + 1 * (1 * 0 + 0 * 1))
        (u22 + 1 * (0 ^ 2 + 1 ^ 2)) ((-d 0 - μ 0) + 1 * μ 0 + 0 * μ 1)
        ((-d 1 - μ 1) + 0 * μ 0 + 1 * μ 1)) := by
  have hαne : α ≠ 0 := hα.ne'
  have hα1 : 1 + α ≠ 0 := by positivity
  have ht := pd_update (β := α / (1 + α)) (by positivity) hs hD (K 0 0 / α) (-(K 1 0) / α)
    (K 0 1 / α) (-(K 1 1) / α)
  rw [← ht11, ← ht12, ← ht22] at ht
  have hu := pd_update (β := 1 + α) (by positivity) ht.1 ht.2 (-1 - K 0 0 / (1 + α))
    (K 1 0 / (1 + α)) (-(K 0 1) / (1 + α)) (-1 + K 1 1 / (1 + α))
  rw [← hu11, ← hu12, ← hu22] at hu
  simp only [bellAverageFidelity, phaseIntegral]
  simp_rw [stepO hα B K hB h11 h12 h22 hs hD ht11 ht12 ht22, in_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [← hu11, ← hu12, ← hu22]
  congr 1
  apply conv2c (β := 1) one_pos hu.1 hu.2
  intro z0 z1
  simp only [one_mul]
  congr 2 <;> field_simp <;> ring

theorem Fspec {α b c : ℝ} (hα : 0 < α) (S G : QuadratureMatrix) (hG : G 1 0 = G 0 1)
    (hs : 0 < (b - c ^ 2 / α) * (S 0 0 ^ 2 + S 0 1 ^ 2) + G 0 0)
    (hD : 0 < ((b - c ^ 2 / α) * (S 0 0 ^ 2 + S 0 1 ^ 2) + G 0 0) *
        ((b - c ^ 2 / α) * (S 1 0 ^ 2 + S 1 1 ^ 2) + G 1 1) -
        ((b - c ^ 2 / α) * (S 0 0 * S 1 0 + S 0 1 * S 1 1) + G 0 1) ^ 2)
    (μ d : PhasePoint) :
    bellAverageFidelity 1 μ (resourceWigner (bobCov (α • (1 : QuadratureMatrix)) (b • (1 : QuadratureMatrix))
        !![-c, 0; 0, c] S G) d) =
      2 * Real.pi * (1 * G2 (2 + α - 2 * c * S 0 0 + b * (S 0 0 ^ 2 + S 0 1 ^ 2) + G 0 0)
        (-c * (S 1 0 + S 0 1) + b * (S 0 0 * S 1 0 + S 0 1 * S 1 1) + G 0 1)
        (2 + α - 2 * c * S 1 1 + b * (S 1 0 ^ 2 + S 1 1 ^ 2) + G 1 1) (-d 0) (-d 1)) := by
  have hαne : α ≠ 0 := hα.ne'
  have hα1 : 1 + α ≠ 0 := by positivity
  unfold bobCov
  have hB : (S * (b • (1 : QuadratureMatrix)) * Sᵀ + G) 1 0 = (S * (b • (1 : QuadratureMatrix)) * Sᵀ + G) 0 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, hG, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring
  have hs' : 0 < (S * (b • (1 : QuadratureMatrix)) * Sᵀ + G) 0 0 -
      (((!![-c, 0; 0, c] * Sᵀ : QuadratureMatrix) 0 0) ^ 2 + ((!![-c, 0; 0, c] * Sᵀ : QuadratureMatrix) 1 0) ^ 2) / α := by
    convert hs using 1
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  have hD' : 0 < ((S * (b • (1 : QuadratureMatrix)) * Sᵀ + G) 0 0 -
      (((!![-c, 0; 0, c] * Sᵀ : QuadratureMatrix) 0 0) ^ 2 + ((!![-c, 0; 0, c] * Sᵀ : QuadratureMatrix) 1 0) ^ 2) / α) *
      ((S * (b • (1 : QuadratureMatrix)) * Sᵀ + G) 1 1 -
      (((!![-c, 0; 0, c] * Sᵀ : QuadratureMatrix) 0 1) ^ 2 + ((!![-c, 0; 0, c] * Sᵀ : QuadratureMatrix) 1 1) ^ 2) / α) -
      ((S * (b • (1 : QuadratureMatrix)) * Sᵀ + G) 0 1 -
      (((!![-c, 0; 0, c] * Sᵀ : QuadratureMatrix) 0 0) * ((!![-c, 0; 0, c] * Sᵀ : QuadratureMatrix) 0 1) +
        ((!![-c, 0; 0, c] * Sᵀ : QuadratureMatrix) 1 0) * ((!![-c, 0; 0, c] * Sᵀ : QuadratureMatrix) 1 1)) / α) ^ 2 := by
    convert hD using 1
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  rw [MF hα _ _ hB rfl rfl rfl hs' hD' rfl rfl rfl rfl rfl rfl μ d]
  congr 3 <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem F_lt {a b c x y : ℝ} (ha : 0 < a) (hD : 16 < a * c - b ^ 2) :
    2 * Real.pi * (1 * G2 a b c x y) < 1 / 2 := by
  have hD0 : 0 < a * c - b ^ 2 := by linarith
  have hq := pdform_nonneg ha hD0 x y
  unfold G2
  have hsq : 4 < Real.sqrt (a * c - b ^ 2) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hD
  have he : Real.exp (-((c * x ^ 2 - 2 * b * x * y + a * y ^ 2) / (a * c - b ^ 2))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (c * x ^ 2 - 2 * b * x * y + a * y ^ 2) / (a * c - b ^ 2) := by positivity
    linarith
  have hpi := Real.pi_pos
  have hs0 : 0 < Real.sqrt (a * c - b ^ 2) := by linarith
  rw [one_mul, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith [Real.exp_pos (-((c * x ^ 2 - 2 * b * x * y + a * y ^ 2) / (a * c - b ^ 2)))]

theorem F_gt {a b c x y : ℝ} (hD0 : 0 < a * c - b ^ 2) (hD : a * c - b ^ 2 < 16) (hx : x = 0)
    (hy : y = 0) : 1 / 2 < 2 * Real.pi * (1 * G2 a b c x y) := by
  subst hx hy
  unfold G2
  have hsq : Real.sqrt (a * c - b ^ 2) < 4 := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hD0.le hD
  have hpi := Real.pi_pos
  have hs0 : 0 < Real.sqrt (a * c - b ^ 2) := Real.sqrt_pos.mpr hD0
  simp only [one_mul, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero, zero_div,
    neg_zero, Real.exp_zero]
  rw [← mul_div_assoc, mul_one, lt_div_iff₀ (by positivity)]
  nlinarith

theorem symp_det (p q u v : ℝ) (h : p * v - q * u = 1) :
    16 < (2 + 221 / 220 - 2 * (21 / 220) * p + 331 / 220 * (p ^ 2 + q ^ 2)) *
        (2 + 221 / 220 - 2 * (21 / 220) * v + 331 / 220 * (u ^ 2 + v ^ 2)) -
      (-(21 / 220) * (u + q) + 331 / 220 * (p * u + q * v)) ^ 2 := by
  have e1 : (2 + 221 / 220 - 2 * (21 / 220) * p + 331 / 220 * (p ^ 2 + q ^ 2)) *
        (2 + 221 / 220 - 2 * (21 / 220) * v + 331 / 220 * (u ^ 2 + v ^ 2)) -
      (-(21 / 220) * (u + q) + 331 / 220 * (p * u + q * v)) ^ 2 =
      (2 + 221 / 220 - (21 / 220) ^ 2 / (331 / 220)) ^ 2 +
        (2 + 221 / 220 - (21 / 220) ^ 2 / (331 / 220)) * (331 / 220) *
          ((p - 21 / 331) ^ 2 + q ^ 2 + u ^ 2 + (v - 21 / 331) ^ 2) +
        (331 / 220) ^ 2 * ((p - 21 / 331) * (v - 21 / 331) - q * u) ^ 2 := by
    ring
  have e2 : 2 * (1 - 21 / 331) ^ 2 ≤ (p - 21 / 331) ^ 2 + q ^ 2 + u ^ 2 + (v - 21 / 331) ^ 2 := by
    rcases le_or_gt (p + v) 2 with hs | hs
    · nlinarith [sq_nonneg (p - v), sq_nonneg (q + u)]
    · have h1 : 0 < (p + v - 2) * (p + v + 2 - 2 * (21 / 331)) := by
        apply mul_pos <;> linarith
      nlinarith [sq_nonneg (q - u)]
  rw [e1]
  nlinarith [sq_nonneg ((p - 21 / 331) * (v - 21 / 331) - q * u)]

theorem r0_A : exampleA (Real.log (11 / 10) / 2) = 221 / 220 := by
  unfold exampleA
  rw [show 2 * (Real.log (11 / 10) / 2) = Real.log (11 / 10) by ring, Real.cosh_eq, Real.exp_neg,
    Real.exp_log (by norm_num)]
  norm_num

theorem r0_C : exampleC (Real.log (11 / 10) / 2) = 21 / 220 := by
  unfold exampleC
  rw [show 2 * (Real.log (11 / 10) / 2) = Real.log (11 / 10) by ring, Real.sinh_eq, Real.exp_neg,
    Real.exp_log (by norm_num)]
  norm_num

theorem r0_B : exampleB (Real.log (11 / 10) / 2) = 331 / 220 := by
  unfold exampleB; rw [r0_A]; norm_num

theorem r0_gain : dampingGain (Real.log (11 / 10) / 2) = 7 / 37 := by
  have hthr : Real.log (11 / 10) / 2 ≤ squeezingThreshold := by
    unfold squeezingThreshold
    rw [one_div, Real.log_inv, neg_neg]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 11 / 10) (by norm_num : (11 / 10 : ℝ) ≤ 2)
    linarith
  unfold dampingGain
  rw [if_pos hthr, r0_C, r0_B]
  norm_num

theorem dissipative_main
    (hP : PhysicalResource (exampleResource (Real.log (11 / 10) / 2)))
    (hG : GaussianCP ((7 / 37 : ℝ) • (1 : QuadratureMatrix)) ((1 - (7 / 37 : ℝ) ^ 2) • (1 : QuadratureMatrix))) :
    ∃ r : ℝ, 0 < r ∧ r < -Real.log (3 / 4) / 2 ∧
      let t := dampingGain r
      let W := exampleOutput r (t • (1 : QuadratureMatrix)) (dampingNoise r) 0
      PhysicalResource (exampleResource r) ∧ GaussianCP (t • (1 : QuadratureMatrix)) (dampingNoise r) ∧
      t < 1 ∧ ∀ mean : PhasePoint, 1 / 2 < bellAverageFidelity 1 mean W ∧
        ∀ (S : QuadratureMatrix) (d : PhasePoint), Symplectic S →
          bellAverageFidelity 1 mean (exampleOutput r S 0 d) < 1 / 2 ∧
          bellAverageFidelity 1 mean (exampleOutput r S 0 d) < bellAverageFidelity 1 mean W := by
  refine ⟨Real.log (11 / 10) / 2, ?_, ?_, ?_⟩
  · have := Real.log_pos (by norm_num : (1 : ℝ) < 11 / 10); positivity
  · rw [show -Real.log (3 / 4) = Real.log (4 / 3) by rw [← Real.log_inv]; norm_num]
    have := Real.log_lt_log (by norm_num) (by norm_num : (11 / 10 : ℝ) < 4 / 3)
    have := Real.log_pos (by norm_num : (1 : ℝ) < 11 / 10)
    linarith
  dsimp only
  unfold dampingNoise
  rw [r0_gain]
  have hW : ∀ mean : PhasePoint, 1 / 2 < bellAverageFidelity 1 mean
      (exampleOutput (Real.log (11 / 10) / 2) ((7 / 37 : ℝ) • (1 : QuadratureMatrix))
        ((1 - (7 / 37 : ℝ) ^ 2) • (1 : QuadratureMatrix)) 0) := by
    intro mean
    unfold exampleOutput
    rw [r0_A, r0_B, r0_C]
    rw [Fspec (by norm_num) _ _ (by simp) (by simp; norm_num) (by simp; norm_num) mean 0]
    apply F_gt <;> simp <;> norm_num
  refine ⟨hP, hG, by norm_num, fun mean => ⟨hW mean, fun S d hS => ?_⟩⟩
  have hdet : S 0 0 * S 1 1 - S 0 1 * S 1 0 = 1 := by
    have := congrArg (fun M => M 0 1) hS
    simp [modeSymplecticForm, Matrix.mul_apply, Fin.sum_univ_two] at this
    linarith
  have hpq : 0 < S 0 0 ^ 2 + S 0 1 ^ 2 := by
    rcases (eq_or_ne (S 0 0) 0) with h0 | h0
    · have : S 0 1 ≠ 0 := by intro h1; rw [h0, h1] at hdet; simp at hdet
      positivity
    · positivity
  have hlt : bellAverageFidelity 1 mean (exampleOutput (Real.log (11 / 10) / 2) S 0 d) < 1 / 2 := by
    unfold exampleOutput
    rw [r0_A, r0_B, r0_C]
    rw [Fspec (by norm_num) _ _ (by simp) (by simp; positivity) (by
      simp only [Matrix.zero_apply, add_zero]
      have e : (331 / 220 - (21 / 220 : ℝ) ^ 2 / (221 / 220)) * (S 0 0 ^ 2 + S 0 1 ^ 2) *
          ((331 / 220 - (21 / 220 : ℝ) ^ 2 / (221 / 220)) * (S 1 0 ^ 2 + S 1 1 ^ 2)) -
          ((331 / 220 - (21 / 220 : ℝ) ^ 2 / (221 / 220)) * (S 0 0 * S 1 0 + S 0 1 * S 1 1)) ^ 2 =
          (331 / 220 - (21 / 220 : ℝ) ^ 2 / (221 / 220)) ^ 2 * (S 0 0 * S 1 1 - S 0 1 * S 1 0) ^ 2 := by
        ring
      rw [e, hdet]; norm_num) mean d]
    have hsd := symp_det (S 0 0) (S 0 1) (S 1 0) (S 1 1) hdet
    apply F_lt
    · simp only [Matrix.zero_apply, add_zero]
      nlinarith [sq_nonneg (S 0 0 - 21 / 331), sq_nonneg (S 0 1)]
    · simp only [Matrix.zero_apply, add_zero]
      linarith
  exact ⟨hlt, lt_trans hlt (hW mean)⟩

theorem physRes : PhysicalResource (exampleResource (Real.log (11 / 10) / 2)) := by
  unfold PhysicalResource QAlgorithms.Papers.Independent.Dependency50.P10.physicalCovariance
    exampleResource standardCov resourceCov
  rw [r0_A, r0_B, r0_C]
  refine ⟨?_, ?_⟩
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
  · have hM : QAlgorithms.Papers.Independent.Dependency50.P10.complexify
          (Matrix.fromBlocks ((221 / 220 : ℝ) • (1 : QuadratureMatrix)) !![-(21 / 220 : ℝ), 0; 0, 21 / 220]
            (!![-(21 / 220 : ℝ), 0; 0, 21 / 220])ᵀ ((331 / 220 : ℝ) • (1 : QuadratureMatrix))) -
        Complex.I • QAlgorithms.Papers.Independent.Dependency50.P10.complexify
          (Matrix.fromBlocks modeSymplecticForm 0 0 modeSymplecticForm) =
        (Matrix.fromBlocks !![(1 : ℂ), -Complex.I; 1, Complex.I]
            !![-((1 / 21 : ℝ) : ℂ), -((1 / 21 : ℝ) : ℂ) * Complex.I; 0, 0]
            !![-((21 / 551 : ℝ) : ℂ), -((21 / 551 : ℝ) : ℂ) * Complex.I; 0, 0]
            !![(1 : ℂ), -Complex.I; 1, Complex.I])ᴴ *
          Matrix.diagonal (Sum.elim ![(441 / 440 : ℂ), 1 / 2204] ![(551 / 440 : ℂ), 1 / 4]) *
          Matrix.fromBlocks !![(1 : ℂ), -Complex.I; 1, Complex.I]
            !![-((1 / 21 : ℝ) : ℂ), -((1 / 21 : ℝ) : ℂ) * Complex.I; 0, 0]
            !![-((21 / 551 : ℝ) : ℂ), -((21 / 551 : ℝ) : ℂ) * Complex.I; 0, 0]
            !![(1 : ℂ), -Complex.I; 1, Complex.I] := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm,
          Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.diagonal] <;>
        apply Complex.ext <;> simp [Complex.conj_ofNat] <;> norm_num
    rw [hM]
    apply Matrix.PosSemidef.conjTranspose_mul_mul_same
    apply Matrix.PosSemidef.diagonal
    intro k
    rcases k with k | k <;> fin_cases k <;> simp [Complex.le_def] <;> norm_num

theorem gaussCP :
    GaussianCP ((7 / 37 : ℝ) • (1 : QuadratureMatrix)) ((1 - (7 / 37 : ℝ) ^ 2) • (1 : QuadratureMatrix)) := by
  unfold GaussianCP
  refine ⟨by simp, ?_⟩
  have hM : QAlgorithms.Papers.Independent.Dependency50.P10.complexify
        ((1 - (7 / 37 : ℝ) ^ 2) • (1 : QuadratureMatrix)) +
      Complex.I • QAlgorithms.Papers.Independent.Dependency50.P10.complexify
        (modeSymplecticForm - (7 / 37 : ℝ) • (1 : QuadratureMatrix) * modeSymplecticForm *
          ((7 / 37 : ℝ) • (1 : QuadratureMatrix))ᵀ) =
      (!![(1 : ℂ), Complex.I; 0, 0])ᴴ * Matrix.diagonal ![((1 - (7 / 37 : ℝ) ^ 2 : ℝ) : ℂ), 0] *
        !![(1 : ℂ), Complex.I; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;>
      apply Complex.ext <;> simp <;> norm_num
  rw [hM]
  apply Matrix.PosSemidef.conjTranspose_mul_mul_same
  apply Matrix.PosSemidef.diagonal
  intro k
  fin_cases k <;> simp [Complex.le_def] <;> norm_num

end P44Aux

open QAlgorithms.Papers.Independent.Claimed50.P44 in
theorem solution :
    ∃ r : ℝ, 0 < r ∧ r < -Real.log (3 / 4) / 2 ∧
      let t := dampingGain r
      let W := exampleOutput r (t • (1 : QuadratureMatrix)) (dampingNoise r) 0
      PhysicalResource (exampleResource r) ∧ GaussianCP (t • (1 : QuadratureMatrix)) (dampingNoise r) ∧
      t < 1 ∧ ∀ mean : PhasePoint, 1 / 2 < bellAverageFidelity 1 mean W ∧
        ∀ (S : QuadratureMatrix) (d : PhasePoint), Symplectic S →
          bellAverageFidelity 1 mean (exampleOutput r S 0 d) < 1 / 2 ∧
          bellAverageFidelity 1 mean (exampleOutput r S 0 d) < bellAverageFidelity 1 mean W := by
  exact P44Aux.dissipative_main P44Aux.physRes P44Aux.gaussCP

end
