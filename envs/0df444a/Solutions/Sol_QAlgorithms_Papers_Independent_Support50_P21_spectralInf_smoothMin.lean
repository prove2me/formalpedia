-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P21.spectralInf_smoothMin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:06:11.6107+00:00
-- url     : https://prove2.me/submissions/cdb8c62e-1c11-4814-808a-41046689730f

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

section X5mod_SM_Core
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace X5SM

variable {I : Type} [Fintype I] [DecidableEq I]

lemma sa_herm {X : Matrix I I ℂ} (h : IsSelfAdjoint X) : Xᴴ = X := h

lemma psd_re {X : Matrix I I ℂ} (h : X.PosSemidef) : 0 ≤ X.trace.re := by
  have := h.trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

lemma conj_psd {X : Matrix I I ℂ} (h : X.PosSemidef) (Y : Matrix I I ℂ) :
    (Y * X * Yᴴ).PosSemidef := h.mul_mul_conjTranspose_same Y

/-- trace of a product of PSD matrices has nonnegative real part -/
lemma tr_mul_psd {A X : Matrix I I ℂ} (hA : A.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (A * X).trace.re := by
  have hX0 : 0 ≤ X := hX.nonneg
  set Y := CFC.sqrt X
  have hY : Yᴴ * Y = X := by
    rw [sa_herm (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X))]; exact CFC.sqrt_mul_sqrt_self X
  rw [← hY]
  have : (A * (Yᴴ * Y)).trace = (Y * A * Yᴴ).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [this]; exact psd_re (conj_psd hA Y)

lemma re_tr_swap (X Y : Matrix I I ℂ) : (Yᴴ * X).trace.re = (Xᴴ * Y).trace.re := by
  have : Yᴴ * X = (Xᴴ * Y)ᴴ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [this, Matrix.trace_conjTranspose]; simp

/-- AM-GM for the Frobenius pairing -/
lemma amgm (X Y : Matrix I I ℂ) {u : ℝ} (hu : 0 < u) :
    (Xᴴ * Y).trace.re + (Yᴴ * X).trace.re ≤ u⁻¹ * (Xᴴ * X).trace.re + u * (Yᴴ * Y).trace.re := by
  set Z := X - (u : ℂ) • Y
  have h0 := psd_re (Matrix.posSemidef_conjTranspose_mul_self Z)
  have e : Zᴴ * Z = Xᴴ * X - (u : ℂ) • (Xᴴ * Y) - (u : ℂ) • (Yᴴ * X) + ((u : ℂ) * u) • (Yᴴ * Y) := by
    simp only [Z, conjTranspose_sub, conjTranspose_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_ofReal]
    module
  rw [e] at h0
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Complex.add_re,
    Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    mul_zero] at h0
  have h1 : 0 ≤ u * (Xᴴ * X).trace.re - u * u * ((Xᴴ * Y).trace.re + (Yᴴ * X).trace.re) +
      u * u * u * (Yᴴ * Y).trace.re := by nlinarith
  have h2 : 0 ≤ (Xᴴ * X).trace.re - u * ((Xᴴ * Y).trace.re + (Yᴴ * X).trace.re) +
      u * u * (Yᴴ * Y).trace.re := by nlinarith
  rw [← sub_nonneg]
  have : u⁻¹ * (Xᴴ * X).trace.re + u * (Yᴴ * Y).trace.re -
      ((Xᴴ * Y).trace.re + (Yᴴ * X).trace.re) =
      u⁻¹ * ((Xᴴ * X).trace.re - u * ((Xᴴ * Y).trace.re + (Yᴴ * X).trace.re) +
      u * u * (Yᴴ * Y).trace.re) := by field_simp; ring
  rw [this]; exact mul_nonneg (inv_nonneg.mpr hu.le) h2

noncomputable def sgn (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

/-- trace norm of a Hermitian matrix is a pairing with a self-adjoint unitary -/
lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma tn_eq {D : Matrix I I ℂ} (hD : D.IsHermitian) :
    QAlgorithms.traceNorm D = (cfc sgn D * D).trace.re ∧ (cfc sgn D)ᴴ = cfc sgn D ∧
      cfc sgn D * cfc sgn D = 1 := by
  have hsa : IsSelfAdjoint D := hD.isSelfAdjoint
  refine ⟨?_, sa_herm (cfc_predicate sgn D), ?_⟩
  · unfold QAlgorithms.traceNorm
    have e1 : Dᴴ * D = cfc (fun x : ℝ => x ^ 2) D := by
      rw [hD.eq, cfc_pow_id D 2 hsa, sq]
    have e2 : cfc Real.sqrt (Dᴴ * D) = cfc sgn D * D := by
      rw [e1, ← cfc_comp' Real.sqrt _ D (Real.continuous_sqrt.continuousOn)]
      rw [show cfc sgn D * D = cfc sgn D * cfc (fun x : ℝ => x) D by rw [cfc_id' ℝ D hsa],
        ← cfc_mul sgn (fun x => x) D (fin _ _) (fin _ _)]
      refine cfc_congr fun x _ => ?_
      simp only [Function.comp, sgn]
      rw [Real.sqrt_sq_eq_abs]
      split_ifs with h
      · rw [abs_of_nonneg h, one_mul]
      · rw [abs_of_neg (not_le.mp h)]; ring
    rw [e2]
  · rw [← cfc_mul sgn sgn D (fin _ _) (fin _ _)]
    rw [show (fun x => sgn x * sgn x) = fun _ => (1 : ℝ) by
      funext x; unfold sgn; split_ifs <;> norm_num]
    exact cfc_const_one ℝ D

end X5SM
end X5mod_SM_Core

section X5mod_SM_Gen
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace X5SM

variable {I : Type} [Fintype I] [DecidableEq I]

section
variable (ρ S Δ : Matrix I I ℂ) (η : ℝ)

noncomputable def T : Matrix I I ℂ := S + Δ + (η : ℂ) • 1
noncomputable def B : Matrix I I ℂ := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (T S Δ η)
noncomputable def G : Matrix I I ℂ := CFC.sqrt S * B S Δ η
end

variable {ρ S Δ : Matrix I I ℂ} {η : ℝ}
  (hρ : ρ.PosSemidef) (hS : S.PosSemidef) (hΔ : Δ.PosSemidef) (hη : 0 < η)
  (hdom : (S + Δ - ρ).PosSemidef)

lemma A_herm (S : Matrix I I ℂ) : (CFC.sqrt S)ᴴ = CFC.sqrt S :=
  sa_herm (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg S))

lemma B_herm (S Δ : Matrix I I ℂ) (η : ℝ) : (B S Δ η)ᴴ = B S Δ η := sa_herm (cfc_predicate _ _)

include hS hΔ hη

lemma T_sub : (T S Δ η - S).PosSemidef := by
  have : T S Δ η - S = Δ + (η : ℂ) • 1 := by unfold T; abel
  rw [this]
  exact hΔ.add (Matrix.PosSemidef.one.smul (by exact_mod_cast hη.le))

lemma T_posdef : (T S Δ η).PosDef := by
  unfold T
  rw [add_assoc]
  exact Matrix.PosDef.posSemidef_add hS
    (Matrix.PosDef.posSemidef_add hΔ (Matrix.PosDef.one.smul (by exact_mod_cast hη)))

lemma T_spec : ∀ x ∈ spectrum ℝ (T S Δ η), 0 < x := by
  intro x hx
  have hT := T_posdef hS hΔ hη
  rw [hT.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hT.eigenvalues_pos i

lemma T_nonneg : 0 ≤ T S Δ η := (T_posdef hS hΔ hη).posSemidef.nonneg

lemma BTB : B S Δ η * T S Δ η * B S Δ η = 1 := by
  have hsa : IsSelfAdjoint (T S Δ η) := (T_posdef hS hΔ hη).1.isSelfAdjoint
  have e : B S Δ η * T S Δ η * B S Δ η =
      cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) (T S Δ η) := by
    rw [cfc_mul _ _ _ (fin _ _) (fin _ _), cfc_mul _ _ _ (fin _ _) (fin _ _), cfc_id' ℝ _ hsa]; rfl
  rw [e, ← cfc_const_one ℝ (T S Δ η)]
  refine cfc_congr fun x hx => ?_
  have hx0 : 0 < x := T_spec hS hΔ hη x hx
  have := Real.mul_self_sqrt hx0.le
  have h2 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  field_simp
  linarith

lemma BT : B S Δ η * T S Δ η = CFC.sqrt (T S Δ η) := by
  have hsa : IsSelfAdjoint (T S Δ η) := (T_posdef hS hΔ hη).1.isSelfAdjoint
  rw [CFC.sqrt_eq_real_sqrt _ (T_nonneg hS hΔ hη), cfcₙ_eq_cfc (hf0 := by simp)]
  have e : B S Δ η * T S Δ η = cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * x) (T S Δ η) := by
    rw [cfc_mul _ _ _ (fin _ _) (fin _ _), cfc_id' ℝ _ hsa]; rfl
  rw [e]
  refine cfc_congr fun x hx => ?_
  have hx0 : 0 < x := T_spec hS hΔ hη x hx
  have := Real.mul_self_sqrt hx0.le
  have h2 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  field_simp
  linarith

lemma TB : T S Δ η * B S Δ η = CFC.sqrt (T S Δ η) := by
  have h := congrArg Matrix.conjTranspose (BT hS hΔ hη)
  rw [conjTranspose_mul, B_herm, (T_posdef hS hΔ hη).1.eq,
    sa_herm (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (T S Δ η)))] at h
  exact h

lemma G_herm : (G S Δ η)ᴴ = B S Δ η * CFC.sqrt S := by
  unfold G; rw [conjTranspose_mul, B_herm, A_herm]

lemma GTG : G S Δ η * T S Δ η * (G S Δ η)ᴴ = S := by
  rw [G_herm hS hΔ hη]; unfold G
  have := BTB hS hΔ hη
  calc CFC.sqrt S * B S Δ η * T S Δ η * (B S Δ η * CFC.sqrt S)
      = CFC.sqrt S * (B S Δ η * T S Δ η * B S Δ η) * CFC.sqrt S := by
        simp only [Matrix.mul_assoc]
    _ = S := by rw [this, Matrix.mul_one, CFC.sqrt_mul_sqrt_self S hS.nonneg]

lemma one_sub_GG : (1 - (G S Δ η)ᴴ * G S Δ η).PosSemidef := by
  have e : 1 - (G S Δ η)ᴴ * G S Δ η = B S Δ η * (T S Δ η - S) * (B S Δ η)ᴴ := by
    rw [G_herm hS hΔ hη, B_herm, Matrix.mul_sub, Matrix.sub_mul, BTB hS hΔ hη]
    unfold G
    rw [← CFC.sqrt_mul_sqrt_self S hS.nonneg]
    simp only [Matrix.mul_assoc]
    rw [CFC.sqrt_mul_sqrt_self S hS.nonneg]
  rw [e]; exact conj_psd (T_sub hS hΔ hη) _

/-- the key trace bound -/
lemma KTK : ((1 - G S Δ η) * T S Δ η * (1 - G S Δ η)ᴴ).trace.re ≤ Δ.trace.re + η * Fintype.card I := by
  set A := CFC.sqrt S
  set C := CFC.sqrt (T S Δ η)
  have e : (1 - G S Δ η) * T S Δ η * (1 - G S Δ η)ᴴ =
      T S Δ η - A * C - C * A + S := by
    have h1 : G S Δ η * T S Δ η = A * C := by unfold G; rw [Matrix.mul_assoc, BT hS hΔ hη]
    have h2 : T S Δ η * (G S Δ η)ᴴ = C * A := by
      rw [G_herm hS hΔ hη, ← Matrix.mul_assoc, TB hS hΔ hη]
    have h3 : (1 - G S Δ η) * T S Δ η * (1 - G S Δ η)ᴴ = T S Δ η - G S Δ η * T S Δ η -
        T S Δ η * (G S Δ η)ᴴ + G S Δ η * T S Δ η * (G S Δ η)ᴴ := by
      simp only [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [h3, GTG hS hΔ hη, h1, h2]
  rw [e]
  have hAC : (A * A).trace.re ≤ (A * C).trace.re := by
    have hle : A ≤ C := CFC.sqrt_le_sqrt S (T S Δ η) (Matrix.le_iff.mpr (T_sub hS hΔ hη))
    have := tr_mul_psd (CFC.sqrt_nonneg S).posSemidef (Matrix.le_iff.mp hle)
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at this
    linarith
  have hCA : (C * A).trace = (A * C).trace := Matrix.trace_mul_comm _ _
  have hAA : A * A = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hT : (T S Δ η).trace.re = S.trace.re + Δ.trace.re + η * Fintype.card I := by
    unfold T; simp [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, hCA]
  rw [hAA] at hAC
  linarith

end X5SM
end X5mod_SM_Gen

section X5mod_SM_Approx
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace X5SM

variable {I : Type} [Fintype I] [DecidableEq I]

lemma trW {W ρ : Matrix I I ℂ} (hW : Wᴴ = W) (hWW : W * W = ρ) (P Q : Matrix I I ℂ) :
    ((P * W)ᴴ * (Q * W)).trace = (Pᴴ * Q * ρ).trace := by
  rw [conjTranspose_mul, hW, ← hWW]
  rw [show W * Pᴴ * (Q * W) = W * (Pᴴ * Q * W) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm W]
  simp only [Matrix.mul_assoc]

variable {ρ S Δ : Matrix I I ℂ} {η : ℝ}

theorem approx (hρ : ρ.PosSemidef) (hρ1 : ρ.trace.re = 1) (hS : S.PosSemidef) (hΔ : Δ.PosSemidef)
    (hη : 0 < η) (hdom : (S + Δ - ρ).PosSemidef) [Nonempty I] :
    (G S Δ η * ρ * (G S Δ η)ᴴ).PosSemidef ∧ (S - G S Δ η * ρ * (G S Δ η)ᴴ).PosSemidef ∧
      (G S Δ η * ρ * (G S Δ η)ᴴ).trace.re ≤ ρ.trace.re ∧
      QAlgorithms.traceNorm (G S Δ η * ρ * (G S Δ η)ᴴ - ρ) ≤
        2 * Real.sqrt (Δ.trace.re + η * Fintype.card I) := by
  set G0 := G S Δ η
  set T0 := T S Δ η
  set r := G0 * ρ * G0ᴴ
  have hTρ : (T0 - ρ).PosSemidef := by
    have : T0 - ρ = (S + Δ - ρ) + (η : ℂ) • 1 := by simp only [T0, T]; abel
    rw [this]; exact hdom.add (Matrix.PosSemidef.one.smul (by exact_mod_cast hη.le))
  -- trace of G^H G rho
  have hGG : (G0ᴴ * G0 * ρ).trace.re ≤ ρ.trace.re := by
    have := tr_mul_psd (one_sub_GG hS hΔ hη) hρ
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at this
    linarith
  have htr_r : r.trace = (G0ᴴ * G0 * ρ).trace := by
    simp only [r]; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  refine ⟨conj_psd hρ G0, ?_, ?_, ?_⟩
  · have : S - r = G0 * (T0 - ρ) * G0ᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, GTG hS hΔ hη]
    rw [this]; exact conj_psd hTρ G0
  · rw [htr_r]; exact hGG
  · -- trace norm
    have hD : (r - ρ).IsHermitian := (conj_psd hρ G0).1.sub hρ.1
    obtain ⟨htn, hUh, hUU⟩ := tn_eq hD
    set U := cfc sgn (r - ρ)
    set V := -U
    have hVh : Vᴴ = V := by simp only [V, conjTranspose_neg, hUh]
    have hVV : Vᴴ * V = 1 := by rw [hVh]; simp only [V, neg_mul_neg, hUU]
    set W := CFC.sqrt ρ
    have hW : Wᴴ = W := A_herm ρ
    have hWW : W * W = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
    set K := 1 - G0
    have hsplit : U * (r - ρ) = V * (K * ρ) + V * (G0 * ρ * Kᴴ) := by
      simp only [V, K, r, conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, neg_mul]
      abel
    set b' := Δ.trace.re + η * Fintype.card I
    have hb'pos : 0 < b' := by
      have := psd_re hΔ
      have : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
      simp only [b']; positivity
    have hb : (Kᴴ * K * ρ).trace.re ≤ b' := by
      have e : (Kᴴ * K * ρ).trace = (K * ρ * Kᴴ).trace := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      have h1 := psd_re (conj_psd hTρ K)
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at h1
      rw [e]; have := KTK hS hΔ hη; linarith
    set u := (Real.sqrt b')⁻¹
    have hu : 0 < u := inv_pos.mpr (Real.sqrt_pos.mpr hb'pos)
    -- first term
    have t1 := amgm (V * W) (K * W) hu
    rw [re_tr_swap (V * W) (K * W), trW hW hWW, trW hW hWW, trW hW hWW, hVV, Matrix.one_mul,
      hVh] at t1
    -- second term
    have t2 := amgm (V * G0 * W) (K * W) hu
    rw [re_tr_swap (K * W) (V * G0 * W), trW hW hWW, trW hW hWW, trW hW hWW] at t2
    have e2 : (Kᴴ * (V * G0) * ρ).trace = (V * (G0 * ρ * Kᴴ)).trace := by
      rw [show Kᴴ * (V * G0) * ρ = Kᴴ * (V * G0 * ρ) by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    have e3 : ((V * G0)ᴴ * (V * G0) * ρ).trace = (G0ᴴ * G0 * ρ).trace := by
      rw [conjTranspose_mul, hVh]
      rw [show G0ᴴ * V * (V * G0) = G0ᴴ * (Vᴴ * V) * G0 by rw [hVh]; simp only [Matrix.mul_assoc],
        hVV, Matrix.mul_one]
    rw [e2, e3] at t2
    have hsum : QAlgorithms.traceNorm (r - ρ) =
        (V * (K * ρ)).trace.re + (V * (G0 * ρ * Kᴴ)).trace.re := by
      rw [htn, hsplit, Matrix.trace_add, Complex.add_re]
    have e1 : (V * K * ρ).trace = (V * (K * ρ)).trace := by rw [Matrix.mul_assoc]
    rw [e1] at t1
    rw [hsum]
    have key : 2 * ((V * (K * ρ)).trace.re + (V * (G0 * ρ * Kᴴ)).trace.re) ≤
        2 * (u⁻¹ + u * b') := by
      have := mul_le_mul_of_nonneg_left hb hu.le
      have := mul_le_mul_of_nonneg_left hGG (inv_nonneg.mpr hu.le)
      rw [hρ1] at *
      nlinarith
    have hsq : u⁻¹ + u * b' = 2 * Real.sqrt b' := by
      simp only [u, inv_inv]
      have h0 : Real.sqrt b' ≠ 0 := (Real.sqrt_pos.mpr hb'pos).ne'
      have := Real.mul_self_sqrt hb'pos.le
      field_simp
      linarith
    linarith

end X5SM
end X5mod_SM_Approx

section X5mod_SM_Thm
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace X5SMT
open X5SM
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (Le traceSmoothMax traceSmoothingBall strictPositive)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

lemma tn_zero : QAlgorithms.traceNorm (0 : Matrix I I ℂ) = 0 := by
  unfold QAlgorithms.traceNorm
  rw [Matrix.mul_zero, cfc_apply_zero]; simp

lemma two_pow (l : ℝ) : (((2 : ℝ) ^ l) : ℂ) = (((2 : ℝ) ^ l : ℝ) : ℂ) := by
  have h : ((2 : ℝ) : ℂ) = algebraMap NNReal ℂ 2 := by
    rw [show algebraMap NNReal ℂ 2 = (((2 : NNReal) : ℝ) : ℂ) from rfl]; simp
  rw [h, CFC.rpow_algebraMap]
  rw [show algebraMap NNReal ℂ ((2 : NNReal) ^ l) = ((((2 : NNReal) ^ l : NNReal) : ℝ) : ℂ) from rfl,
    NNReal.coe_rpow]
  simp

lemma ball_le {eps : ℝ} {rho sigma r : Matrix I I ℂ} (hr : r ∈ traceSmoothingBall eps rho) (l : ℝ)
    (hl : ((((2 : ℝ) ^ l : ℝ) : ℂ) • sigma - r).PosSemidef) :
    traceSmoothMax eps rho sigma ≤ (l : EReal) := by
  unfold traceSmoothMax
  have h1 : sInf {v | ∃ r ∈ traceSmoothingBall eps rho, v = maxRelative r sigma} ≤
      maxRelative r sigma := sInf_le ⟨r, hr, rfl⟩
  refine h1.trans ?_
  unfold maxRelative
  exact sInf_le ⟨l, rfl, hl⟩

theorem main (rho sigma Delta : Matrix I I ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (hDelta : Delta.PosSemidef) (lambda eps : ℝ)
    (hdom : Le rho ((((2 : ℝ) ^ lambda) : ℂ) • sigma + Delta))
    (heps : Real.sqrt (8 * tr Delta) ≤ eps) :
    traceSmoothMax eps rho sigma ≤ (lambda : EReal) := by
  set S := (((2 : ℝ) ^ lambda : ℝ) : ℂ) • sigma
  have hS : S.PosSemidef := hsigma.1.smul (by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ lambda := by positivity
    exact_mod_cast this)
  have hd : (S + Delta - rho).PosSemidef := by
    have := hdom; unfold Le at this; rwa [two_pow] at this
  have hρ1 : rho.trace.re = 1 := by rw [hrho.2]; simp
  have hδ := psd_re hDelta
  have heps0 : 0 ≤ eps := (Real.sqrt_nonneg _).trans heps
  rcases hδ.eq_or_lt with h0 | hpos
  · -- Delta = 0
    have hD0 : Delta = 0 := by
      rw [← hDelta.trace_eq_zero_iff]
      have him : Delta.trace.im = 0 := (Complex.nonneg_iff.mp hDelta.trace_nonneg).2.symm
      exact Complex.ext h0.symm him
    rw [hD0, add_zero] at hd
    refine ball_le ⟨hrho.1, ?_, le_rfl⟩ lambda hd
    rw [sub_self, tn_zero]; exact heps0
  · set η := Delta.trace.re / Fintype.card I
    have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have hη : 0 < η := div_pos hpos hc
    obtain ⟨h1, h2, h3, h4⟩ := approx hrho.1 hρ1 hS hDelta hη hd
    refine ball_le ⟨h1, ?_, h3⟩ lambda h2
    refine h4.trans (le_trans (le_of_eq ?_) heps)
    have e : Delta.trace.re + η * Fintype.card I = 2 * Delta.trace.re := by
      simp only [η]; field_simp; ring
    rw [e]
    unfold tr
    have h8 : Real.sqrt (8 * Delta.trace.re) = 2 * Real.sqrt (2 * Delta.trace.re) := by
      rw [show (8 : ℝ) * Delta.trace.re = 2 ^ 2 * (2 * Delta.trace.re) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [h8]

end X5SMT
end X5mod_SM_Thm

section X5mod_T2_Base
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace X5T2
open X5SM X5SMT
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21
  (Le traceSmoothMax traceSmoothingBall weakPositive)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/-- Lemma 14 with a merely positive semidefinite comparison operator. -/
theorem mainP (rho sigma Delta : Matrix I I ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hsigma : sigma.PosSemidef)
    (hDelta : Delta.PosSemidef) (lambda eps : ℝ)
    (hdom : Le rho ((((2 : ℝ) ^ lambda) : ℂ) • sigma + Delta))
    (heps : Real.sqrt (8 * tr Delta) ≤ eps) :
    traceSmoothMax eps rho sigma ≤ (lambda : EReal) := by
  set S := (((2 : ℝ) ^ lambda : ℝ) : ℂ) • sigma
  have hS : S.PosSemidef := hsigma.smul (by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ lambda := by positivity
    exact_mod_cast this)
  have hd : (S + Delta - rho).PosSemidef := by
    have := hdom; unfold Le at this; rwa [two_pow] at this
  have hρ1 : rho.trace.re = 1 := by rw [hrho.2]; simp
  have hδ := psd_re hDelta
  have heps0 : 0 ≤ eps := (Real.sqrt_nonneg _).trans heps
  rcases hδ.eq_or_lt with h0 | hpos
  · have hD0 : Delta = 0 := by
      rw [← hDelta.trace_eq_zero_iff]
      have him : Delta.trace.im = 0 := (Complex.nonneg_iff.mp hDelta.trace_nonneg).2.symm
      exact Complex.ext h0.symm him
    rw [hD0, add_zero] at hd
    refine ball_le ⟨hrho.1, ?_, le_rfl⟩ lambda hd
    rw [sub_self, tn_zero]; exact heps0
  · set η := Delta.trace.re / Fintype.card I
    have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    have hη : 0 < η := div_pos hpos hc
    obtain ⟨h1, h2, h3, h4⟩ := approx hrho.1 hρ1 hS hDelta hη hd
    refine ball_le ⟨h1, ?_, h3⟩ lambda h2
    refine h4.trans (le_trans (le_of_eq ?_) heps)
    have e : Delta.trace.re + η * Fintype.card I = 2 * Delta.trace.re := by
      simp only [η]; field_simp; ring
    rw [e]
    unfold tr
    have h8 : Real.sqrt (8 * Delta.trace.re) = 2 * Real.sqrt (2 * Delta.trace.re) := by
      rw [show (8 : ℝ) * Delta.trace.re = 2 ^ 2 * (2 * Delta.trace.re) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [h8]

lemma wp_psd (X : Matrix I I ℂ) : (weakPositive X).PosSemidef :=
  (cfc_nonneg (fun x _ => by split_ifs <;> norm_num) :
    0 ≤ cfc (fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0) X).posSemidef

lemma one_sub_wp_psd {X : Matrix I I ℂ} (hX : IsSelfAdjoint X) : (1 - weakPositive X).PosSemidef := by
  have e : 1 - weakPositive X = cfc (fun x : ℝ => 1 - if 0 ≤ x then (1 : ℝ) else 0) X := by
    rw [cfc_sub _ _ _ (fin _ _) (fin _ _), cfc_const_one ℝ X]; rfl
  rw [e]
  exact (cfc_nonneg (fun x _ => by split_ifs <;> norm_num) :
    0 ≤ cfc (fun x : ℝ => 1 - if 0 ≤ x then (1 : ℝ) else 0) X).posSemidef

lemma wp_mul {X : Matrix I I ℂ} (hX : IsSelfAdjoint X) :
    weakPositive X * X = cfc (fun x : ℝ => max x 0) X := by
  have e : weakPositive X * X = cfc (fun x : ℝ => (if 0 ≤ x then (1 : ℝ) else 0) * x) X := by
    unfold weakPositive
    rw [cfc_mul _ _ _ (fin _ _) (fin _ _), cfc_id' ℝ X hX]
  rw [e]
  refine cfc_congr fun x _ => ?_
  split_ifs with h
  · rw [one_mul, max_eq_left h]
  · rw [zero_mul, max_eq_right (not_le.mp h).le]

lemma pos_psd (X : Matrix I I ℂ) : (cfc (fun x : ℝ => max x 0) X).PosSemidef :=
  (cfc_nonneg (fun x _ => le_max_right x 0) : 0 ≤ cfc (fun x : ℝ => max x 0) X).posSemidef

/-- trace pairing with an effect is bounded by the trace norm -/
lemma tr_le_tn {Q Y : Matrix I I ℂ} (hQ : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef)
    (hY : Y.IsHermitian) : tr (Q * Y) ≤ QAlgorithms.traceNorm Y := by
  have hsa : IsSelfAdjoint Y := hY.isSelfAdjoint
  set Yp := cfc (fun x : ℝ => max x 0) Y
  set Ym := cfc (fun x : ℝ => max (-x) 0) Y
  have hYp : Yp.PosSemidef := pos_psd Y
  have hYm : Ym.PosSemidef :=
    (cfc_nonneg (fun x _ => le_max_right (-x) 0) : 0 ≤ cfc (fun x : ℝ => max (-x) 0) Y).posSemidef
  have eY : Y = Yp - Ym := by
    rw [← cfc_sub _ _ _ (fin _ _) (fin _ _)]
    conv_lhs => rw [← cfc_id' ℝ Y hsa]
    refine cfc_congr fun x _ => ?_
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have eN : QAlgorithms.traceNorm Y = (Yp + Ym).trace.re := by
    rw [(tn_eq hY).1]
    congr 2
    rw [← cfc_add _ _ _ (fin _ _) (fin _ _)]
    conv_lhs => rw [show cfc sgn Y * Y = cfc sgn Y * cfc (fun x : ℝ => x) Y by rw [cfc_id' ℝ Y hsa]]
    rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
    refine cfc_congr fun x _ => ?_
    unfold sgn
    rcases le_total 0 x with h | h
    · rw [if_pos h, max_eq_left h, max_eq_right (by linarith)]; ring
    · rcases h.eq_or_lt with h' | h'
      · subst h'; simp
      · rw [if_neg (not_le.mpr h'), max_eq_right h, max_eq_left (by linarith)]; ring
  rw [eN]; unfold tr
  have a1 := tr_mul_psd hQ hYm
  have a2 := tr_mul_psd hQ1 hYp
  have a3 := psd_re hYm
  rw [eY]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_add,
    Complex.sub_re, Complex.add_re] at a2 ⊢
  linarith

lemma tn_neg (Y : Matrix I I ℂ) : QAlgorithms.traceNorm (-Y) = QAlgorithms.traceNorm Y := by
  unfold QAlgorithms.traceNorm; simp

end X5T2
end X5mod_T2_Base

section X5mod_T2_Step
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace X5T2
open X5SM X5SMT
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21
  (Le traceSmoothMax traceSmoothingBall weakPositive)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

lemma S_psd {sigma : Matrix I I ℂ} (hsigma : sigma.PosSemidef) (l : ℝ) :
    ((((2 : ℝ) ^ l : ℝ) : ℂ) • sigma).PosSemidef := hsigma.smul (by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ l := by positivity
    exact_mod_cast this)

lemma mass_bounds {rho sigma : Matrix I I ℂ} (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (lam : ℝ) :
    0 ≤ tr (weakPositive (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma) *
      (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma)) ∧
    tr (weakPositive (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma) *
      (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma)) ≤ 1 := by
  rw [two_pow]
  have hS := S_psd hsigma lam
  set S := (((2 : ℝ) ^ lam : ℝ) : ℂ) • sigma
  set X := rho - S
  have hX : IsSelfAdjoint X := (hrho.1.1.sub hS.1).isSelfAdjoint
  refine ⟨?_, ?_⟩
  · rw [wp_mul hX]; exact psd_re (pos_psd X)
  · have a1 := tr_mul_psd (wp_psd X) hS
    have a2 := tr_mul_psd (one_sub_wp_psd hX) hrho.1
    have hρ1 : rho.trace.re = 1 := by rw [hrho.2]; simp
    unfold tr
    simp only [X, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
      Complex.sub_re] at a2 ⊢
    linarith

lemma dir1 {rho sigma : Matrix I I ℂ} (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (lam eps : ℝ)
    (h : Real.sqrt (8 * tr (weakPositive (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma) *
      (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma))) ≤ eps) :
    traceSmoothMax eps rho sigma ≤ (lam : EReal) := by
  rw [two_pow] at h
  have hS := S_psd hsigma lam
  set S := (((2 : ℝ) ^ lam : ℝ) : ℂ) • sigma
  set X := rho - S
  have hX : IsSelfAdjoint X := (hrho.1.1.sub hS.1).isSelfAdjoint
  rw [wp_mul hX] at h
  refine mainP rho sigma _ hrho hsigma (pos_psd X) lam eps ?_ h
  unfold Le; rw [two_pow]
  have e : S + cfc (fun x : ℝ => max x 0) X - rho = cfc (fun x : ℝ => max x 0 - x) X := by
    rw [cfc_sub _ _ _ (fin _ _) (fin _ _), cfc_id' ℝ X hX]; simp only [X]; abel
  rw [e]
  exact (cfc_nonneg (fun x _ => by simp only [sub_nonneg]; exact le_max_left x 0) :
    0 ≤ cfc (fun x : ℝ => max x 0 - x) X).posSemidef

lemma dir2 {rho sigma : Matrix I I ℂ} (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (lam eps : ℝ)
    (h : traceSmoothMax eps rho sigma < (lam : EReal)) :
    tr (weakPositive (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma) *
      (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma)) ≤ eps := by
  unfold traceSmoothMax at h
  obtain ⟨v, ⟨r, hr, rfl⟩, hv⟩ := sInf_lt_iff.mp h
  unfold maxRelative at hv
  obtain ⟨w, ⟨l, rfl, hl⟩, hw⟩ := sInf_lt_iff.mp hv
  have hl' : l < lam := EReal.coe_lt_coe_iff.mp hw
  rw [two_pow]
  have hS := S_psd hsigma lam
  set S := (((2 : ℝ) ^ lam : ℝ) : ℂ) • sigma
  set X := rho - S
  have hX : IsSelfAdjoint X := (hrho.1.1.sub hS.1).isSelfAdjoint
  have hSr : (S - r).PosSemidef := by
    have e : S - r = ((((2 : ℝ) ^ lam - (2 : ℝ) ^ l : ℝ) : ℂ) • sigma) +
        ((((2 : ℝ) ^ l : ℝ) : ℂ) • sigma - r) := by
      simp only [S, Complex.ofReal_sub, sub_smul]; abel
    rw [e]
    refine Matrix.PosSemidef.add (hsigma.smul ?_) hl
    have : (2 : ℝ) ^ l ≤ (2 : ℝ) ^ lam := Real.rpow_le_rpow_of_exponent_le (by norm_num) hl'.le
    exact_mod_cast (sub_nonneg.mpr this)
  have hY : (-(r - rho)).IsHermitian := by
    rw [neg_sub]; exact hrho.1.1.sub hr.1.1
  have a1 := tr_le_tn (wp_psd X) (one_sub_wp_psd hX) hY
  rw [tn_neg] at a1
  have a2 := tr_mul_psd (wp_psd X) hSr
  have eX : X = -(r - rho) - (S - r) := by simp only [X]; abel
  calc tr (weakPositive X * X) = tr (weakPositive X * -(r - rho)) -
        (weakPositive X * (S - r)).trace.re := by
          unfold tr; rw [eX, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    _ ≤ eps := by linarith [hr.2.1]

end X5T2
end X5mod_T2_Step

section X5mod_T2_Main
open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace X5T2
open X5SM X5SMT
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable (rho sigma : (k : ℕ) → Matrix (PositiveTensorBasis I k) (PositiveTensorBasis I k) ℂ)

lemma mass_nn (hrho : ∀ k, QAlgorithms.IsDensityMatrix (rho k))
    (hsigma : ∀ k, (sigma k).PosSemidef) (γ : ℝ) (k : ℕ) :
    0 ≤ spectralMass rho sigma γ k :=
  (mass_bounds (hrho k) (hsigma k) (((k + 1 : ℕ) : ℝ) * γ)).1

lemma mass_le (hrho : ∀ k, QAlgorithms.IsDensityMatrix (rho k))
    (hsigma : ∀ k, (sigma k).PosSemidef) (γ : ℝ) (k : ℕ) :
    spectralMass rho sigma γ k ≤ 1 :=
  (mass_bounds (hrho k) (hsigma k) (((k + 1 : ℕ) : ℝ) * γ)).2

lemma scale_eq (k : ℕ) (γ : ℝ) :
    (((1 / ((k + 1 : ℕ) : ℝ)) : ℝ) : EReal) * (((((k + 1 : ℕ) : ℝ) * γ) : ℝ) : EReal) = (γ : EReal) := by
  rw [← EReal.coe_mul]; congr 1
  have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  field_simp

lemma coef_nn (k : ℕ) : (0 : EReal) ≤ (((1 / ((k + 1 : ℕ) : ℝ)) : ℝ) : EReal) := by
  exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ))

lemma ub1 (hrho : ∀ k, QAlgorithms.IsDensityMatrix (rho k))
    (hsigma : ∀ k, (sigma k).PosSemidef) (γ : ℝ)
    (hγ : limsup (spectralMass rho sigma γ) atTop = 0) (eps : ℝ) (heps : 0 < eps) :
    maxAsymptotic rho sigma eps ≤ (γ : EReal) := by
  have hb1 : IsBoundedUnder (· ≤ ·) atTop (spectralMass rho sigma γ) :=
    isBoundedUnder_of ⟨1, fun k => mass_le rho sigma hrho hsigma γ k⟩
  have hb0 : IsBoundedUnder (· ≥ ·) atTop (spectralMass rho sigma γ) :=
    isBoundedUnder_of ⟨0, fun k => mass_nn rho sigma hrho hsigma γ k⟩
  have ht : Tendsto (spectralMass rho sigma γ) atTop (𝓝 0) := by
    refine tendsto_of_le_liminf_of_limsup_le ?_ hγ.le hb1 hb0
    exact le_liminf_of_le hb1.isCoboundedUnder_ge
      (Eventually.of_forall fun k => mass_nn rho sigma hrho hsigma γ k)
  have ht2 : Tendsto (fun k => Real.sqrt (8 * spectralMass rho sigma γ k)) atTop (𝓝 0) := by
    have hc : Continuous fun x : ℝ => Real.sqrt (8 * x) :=
      Real.continuous_sqrt.comp (continuous_const.mul continuous_id)
    have := (hc.tendsto 0).comp ht
    simpa [Function.comp_def] using this
  have hev := (tendsto_order.1 ht2).2 eps heps
  unfold maxAsymptotic
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hev] with k hk
  have h1 := dir1 (hrho k) (hsigma k) (((k + 1 : ℕ) : ℝ) * γ) eps hk.le
  calc _ ≤ (((1 / ((k + 1 : ℕ) : ℝ)) : ℝ) : EReal) * (((((k + 1 : ℕ) : ℝ) * γ) : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left h1 (coef_nn k)
    _ = γ := scale_eq k γ

lemma ub2 (hrho : ∀ k, QAlgorithms.IsDensityMatrix (rho k))
    (hsigma : ∀ k, (sigma k).PosSemidef) (γ : ℝ)
    (hγ : ∀ eps : ℝ, 0 < eps → maxAsymptotic rho sigma eps < (γ : EReal)) :
    limsup (spectralMass rho sigma γ) atTop = 0 := by
  have hb1 : IsBoundedUnder (· ≤ ·) atTop (spectralMass rho sigma γ) :=
    isBoundedUnder_of ⟨1, fun k => mass_le rho sigma hrho hsigma γ k⟩
  have hb0 : IsBoundedUnder (· ≥ ·) atTop (spectralMass rho sigma γ) :=
    isBoundedUnder_of ⟨0, fun k => mass_nn rho sigma hrho hsigma γ k⟩
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun eps heps => ?_
    rw [zero_add]
    have hev := eventually_lt_of_limsup_lt (hγ eps heps)
    refine limsup_le_of_le hb0.isCoboundedUnder_le ?_
    filter_upwards [hev] with k hk
    refine dir2 (hrho k) (hsigma k) (((k + 1 : ℕ) : ℝ) * γ) eps ?_
    by_contra hc
    push_neg at hc
    have := mul_le_mul_of_nonneg_left hc (coef_nn k)
    rw [scale_eq] at this
    exact absurd hk (not_lt.mpr this)
  · exact le_limsup_of_frequently_le
      (Frequently.of_forall fun k => mass_nn rho sigma hrho hsigma γ k) hb1

lemma anti : Antitone (maxAsymptotic rho sigma) := by
  intro e1 e2 h
  unfold maxAsymptotic
  refine limsup_le_limsup (Eventually.of_forall fun k => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (coef_nn k)
  refine sInf_le_sInf ?_
  rintro v ⟨r, ⟨h1, h2, h3⟩, rfl⟩
  exact ⟨r, ⟨h1, h2.trans h, h3⟩, rfl⟩

theorem main (hrho : ∀ k, QAlgorithms.IsDensityMatrix (rho k))
    (hsigma : ∀ k, (sigma k).PosSemidef) :
    Tendsto (maxAsymptotic rho sigma) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (spectralSup rho sigma)) := by
  have ht := (anti rho sigma).tendsto_nhdsGT 0
  convert ht using 2
  refine le_antisymm ?_ ?_
  · by_contra hc
    push_neg at hc
    obtain ⟨γ, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    have hmem : limsup (spectralMass rho sigma γ) atTop = 0 :=
      ub2 rho sigma hrho hsigma γ fun eps heps =>
        lt_of_le_of_lt (le_sSup (Set.mem_image_of_mem (maxAsymptotic rho sigma)
          (show eps ∈ Set.Ioi (0 : ℝ) from heps))) h1
    have : spectralSup rho sigma ≤ (γ : EReal) := sInf_le ⟨γ, rfl, hmem⟩
    exact absurd h2 (not_lt.mpr this)
  · refine sSup_le ?_
    rintro _ ⟨eps, heps, rfl⟩
    refine le_sInf ?_
    rintro _ ⟨γ, rfl, hγ⟩
    exact ub1 rho sigma hrho hsigma γ hγ eps heps

end X5T2
end X5mod_T2_Main

section X5mod_T3_Base
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace X5T3
open X5SM X5SMT X5T2
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)
open QAlgorithms.Papers.Independent.Information100.P07 (support operatorRange projection)
open QAlgorithms.Papers.Independent.Support50.P21
  (Le traceSmoothMin traceSmoothingBall weakPositive dMin)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- indicator of nonzero eigenvalues -/
noncomputable def ind : ℝ → ℝ := fun x => if x = 0 then 0 else 1

/-- the support projection as a spectral indicator, with the factorization facts -/
lemma support_facts {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    support X = cfc ind X ∧
      X * cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) X = cfc ind X ∧
      cfc ind X * X = X := by
  have hsa := hX.isSelfAdjoint
  have fin : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ X) := fun f =>
    (Matrix.finite_real_spectrum (A := X)).continuousOn f
  set P := cfc ind X
  set Q := cfc (fun x : ℝ => if x = 0 then 0 else x⁻¹) X
  have hXQ : X * Q = P := by
    have : P = cfc (fun x : ℝ => x * (if x = 0 then 0 else x⁻¹)) X := by
      refine cfc_congr fun x _ => ?_
      simp only [ind]; split_ifs with h
      · simp
      · field_simp
    rw [this, cfc_mul (fun x : ℝ => x) _ X (fin _) (fin _), cfc_id' ℝ X]
  have hPX : P * X = X := by
    rw [show P * X = P * cfc (fun x : ℝ => x) X by rw [cfc_id' ℝ X],
      ← cfc_mul ind (fun x : ℝ => x) X (fin _) (fin _)]
    conv_rhs => rw [← cfc_id' ℝ X]
    refine cfc_congr fun x _ => ?_
    simp only [ind]; split_ifs with h <;> simp [h]
  refine ⟨?_, hXQ, hPX⟩
  have hPh : Pᴴ = P := (cfc_predicate ind X : IsSelfAdjoint P)
  unfold support projection operatorRange
  rw [LinearEquiv.symm_apply_eq]
  refine LinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.coe_coe]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · refine ⟨toEuclideanLin Q x, ?_⟩
    simp only [toLpLin_apply, WithLp.ofLp_toLp, mulVec_mulVec, hXQ]
  · rintro _ ⟨y, rfl⟩
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_sub, star_sub, star_mulVec, hPh,
      dotProduct_sub]
    rw [dotProduct_comm (X *ᵥ _) (star (WithLp.ofLp x) ᵥ* P), ← dotProduct_mulVec, mulVec_mulVec, hPX,
      dotProduct_comm]
    simp

lemma ind_psd (X : Matrix I I ℂ) : (cfc ind X).PosSemidef :=
  (cfc_nonneg (fun x _ => by simp only [ind]; split_ifs <;> norm_num) :
    0 ≤ cfc ind X).posSemidef

lemma one_sub_ind_psd {X : Matrix I I ℂ} (hX : X.IsHermitian) : (1 - cfc ind X).PosSemidef := by
  have e : 1 - cfc ind X = cfc (fun x : ℝ => 1 - ind x) X := by
    rw [cfc_sub _ _ _ (fin _ _) (fin _ _), cfc_const_one ℝ X hX.isSelfAdjoint]
  rw [e]
  exact (cfc_nonneg (fun x _ => by simp only [ind]; split_ifs <;> norm_num) :
    0 ≤ cfc (fun x : ℝ => 1 - ind x) X).posSemidef

lemma wp_herm (X : Matrix I I ℂ) : (weakPositive X)ᴴ = weakPositive X :=
  sa_herm (cfc_predicate _ _)

lemma wp_idem {X : Matrix I I ℂ} (hX : IsSelfAdjoint X) :
    weakPositive X * weakPositive X = weakPositive X := by
  unfold weakPositive
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  refine cfc_congr fun x _ => ?_
  split_ifs <;> norm_num

/-- gentle-operator trace-norm bound for a contraction G0 -/
theorem gentle {ρ G0 : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hρ1 : ρ.trace.re = 1)
    (hG : (1 - G0ᴴ * G0).PosSemidef) {b' : ℝ} (hb'pos : 0 < b')
    (hb : ((1 - G0)ᴴ * (1 - G0) * ρ).trace.re ≤ b') :
    QAlgorithms.traceNorm (G0 * ρ * G0ᴴ - ρ) ≤ 2 * Real.sqrt b' := by
  set r := G0 * ρ * G0ᴴ
  have hGG : (G0ᴴ * G0 * ρ).trace.re ≤ ρ.trace.re := by
    have := tr_mul_psd hG hρ
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at this
    linarith
  have hD : (r - ρ).IsHermitian := (conj_psd hρ G0).1.sub hρ.1
  obtain ⟨htn, hUh, hUU⟩ := tn_eq hD
  set U := cfc sgn (r - ρ)
  set V := -U
  have hVh : Vᴴ = V := by simp only [V, conjTranspose_neg, hUh]
  have hVV : Vᴴ * V = 1 := by rw [hVh]; simp only [V, neg_mul_neg, hUU]
  set W := CFC.sqrt ρ
  have hW : Wᴴ = W := A_herm ρ
  have hWW : W * W = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  set K := 1 - G0
  have hsplit : U * (r - ρ) = V * (K * ρ) + V * (G0 * ρ * Kᴴ) := by
    simp only [V, K, r, conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, neg_mul]
    abel
  set u := (Real.sqrt b')⁻¹
  have hu : 0 < u := inv_pos.mpr (Real.sqrt_pos.mpr hb'pos)
  have t1 := amgm (V * W) (K * W) hu
  rw [re_tr_swap (V * W) (K * W), trW hW hWW, trW hW hWW, trW hW hWW, hVV, Matrix.one_mul,
    hVh] at t1
  have t2 := amgm (V * G0 * W) (K * W) hu
  rw [re_tr_swap (K * W) (V * G0 * W), trW hW hWW, trW hW hWW, trW hW hWW] at t2
  have e2 : (Kᴴ * (V * G0) * ρ).trace = (V * (G0 * ρ * Kᴴ)).trace := by
    rw [show Kᴴ * (V * G0) * ρ = Kᴴ * (V * G0 * ρ) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have e3 : ((V * G0)ᴴ * (V * G0) * ρ).trace = (G0ᴴ * G0 * ρ).trace := by
    rw [conjTranspose_mul, hVh]
    rw [show G0ᴴ * V * (V * G0) = G0ᴴ * (Vᴴ * V) * G0 by rw [hVh]; simp only [Matrix.mul_assoc],
      hVV, Matrix.mul_one]
  rw [e2, e3] at t2
  have hsum : QAlgorithms.traceNorm (r - ρ) =
      (V * (K * ρ)).trace.re + (V * (G0 * ρ * Kᴴ)).trace.re := by
    rw [htn, hsplit, Matrix.trace_add, Complex.add_re]
  have e1 : (V * K * ρ).trace = (V * (K * ρ)).trace := by rw [Matrix.mul_assoc]
  rw [e1] at t1
  rw [hsum]
  have key : 2 * ((V * (K * ρ)).trace.re + (V * (G0 * ρ * Kᴴ)).trace.re) ≤
      2 * (u⁻¹ + u * b') := by
    have := mul_le_mul_of_nonneg_left hb hu.le
    have := mul_le_mul_of_nonneg_left hGG (inv_nonneg.mpr hu.le)
    rw [hρ1] at *
    nlinarith
  have hsq : u⁻¹ + u * b' = 2 * Real.sqrt b' := by
    simp only [u, inv_inv]
    have h0 : Real.sqrt b' ≠ 0 := (Real.sqrt_pos.mpr hb'pos).ne'
    have := Real.mul_self_sqrt hb'pos.le
    field_simp
    linarith
  linarith

variable [Nonempty I]

/-- the positive spectral projector maximizes the pairing over effects -/
lemma effect_le {Q X : Matrix I I ℂ} (hQ : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef)
    (hX : X.IsHermitian) : tr (Q * X) ≤ tr (weakPositive X * X) := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [wp_mul hsa]
  set Xp := cfc (fun x : ℝ => max x 0) X
  set Xm := cfc (fun x : ℝ => max (-x) 0) X
  have hXp : Xp.PosSemidef := pos_psd X
  have hXm : Xm.PosSemidef :=
    (cfc_nonneg (fun x _ => le_max_right (-x) 0) : 0 ≤ cfc (fun x : ℝ => max (-x) 0) X).posSemidef
  have eX : X = Xp - Xm := by
    rw [← cfc_sub _ _ _ (fin _ _) (fin _ _)]
    conv_lhs => rw [← cfc_id' ℝ X hsa]
    refine cfc_congr fun x _ => ?_
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have a1 := tr_mul_psd hQ hXm
  have a2 := tr_mul_psd hQ1 hXp
  unfold tr
  conv_lhs => rw [eX]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    Complex.sub_re] at a2 ⊢
  linarith

/-- lower bound: a nearly full positive part yields a large smooth min-entropy -/
lemma low {rho sigma : Matrix I I ℂ} (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (lam eps : ℝ) (heps : 0 < eps)
    (h : 1 - tr (weakPositive (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma) *
      (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma)) ≤ eps ^ 2 / 4) :
    (lam : EReal) ≤ traceSmoothMin eps rho sigma := by
  have hm0 := (mass_bounds hrho hsigma lam).1
  rw [two_pow] at h hm0
  have hS := S_psd hsigma lam
  set c : ℝ := (2 : ℝ) ^ lam with hc
  have hcpos : 0 < c := by positivity
  set S := ((c : ℝ) : ℂ) • sigma
  set X := rho - S
  have hX : IsSelfAdjoint X := (hrho.1.1.sub hS.1).isSelfAdjoint
  set P := weakPositive X
  have hPh : Pᴴ = P := wp_herm X
  have hPP : P * P = P := wp_idem hX
  have hρ1 : rho.trace.re = 1 := by rw [hrho.2]; simp
  set r := P * rho * Pᴴ
  -- trace bookkeeping
  have hPS : 0 ≤ (P * S).trace.re := tr_mul_psd (wp_psd X) hS
  have hPρ1 : (P * rho).trace.re ≤ 1 := by
    have := tr_mul_psd (one_sub_wp_psd hX) hrho.1
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at this
    linarith
  have hm : tr (P * X) = (P * rho).trace.re - (P * S).trace.re := by
    unfold tr; simp only [X, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have hr_tr : r.trace = (P * rho).trace := by
    simp only [r, hPh]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPP]
  have hmem : r ∈ traceSmoothingBall eps rho := by
    refine ⟨conj_psd hrho.1 P, ?_, ?_⟩
    · have hG : (1 - Pᴴ * P).PosSemidef := by rw [hPh, hPP]; exact one_sub_wp_psd hX
      have hb'pos : 0 < eps ^ 2 / 4 := by positivity
      have hb : ((1 - P)ᴴ * (1 - P) * rho).trace.re ≤ eps ^ 2 / 4 := by
        have e : (1 - P)ᴴ * (1 - P) = 1 - P := by
          rw [conjTranspose_sub, conjTranspose_one, hPh, Matrix.sub_mul, Matrix.mul_sub,
            Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP]; abel
        rw [e, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
        linarith
      have := gentle hrho.1 hρ1 hG hb'pos hb
      have hs : Real.sqrt (eps ^ 2 / 4) = eps / 2 := by
        rw [show eps ^ 2 / 4 = (eps / 2) ^ 2 by ring]; exact Real.sqrt_sq (by linarith)
      rw [hs] at this; linarith
    · unfold tr; rw [hr_tr]; linarith
  refine le_trans ?_ (le_sSup ⟨r, hmem, rfl⟩)
  -- dMin r sigma ≥ lam
  have hrH : r.IsHermitian := (conj_psd hrho.1 P).1
  obtain ⟨hsupp, hXQ, -⟩ := support_facts hrH
  set Pr := cfc ind r
  have hPrh : Prᴴ = Pr := sa_herm (cfc_predicate ind r)
  have hPr : P * r = r := by simp only [r, ← Matrix.mul_assoc, hPP]
  have hPPr : P * Pr = Pr := by rw [← hXQ, ← Matrix.mul_assoc, hPr]
  have hPrP : Pr * P = Pr := by
    have := congrArg conjTranspose hPPr
    rwa [conjTranspose_mul, hPh, hPrh] at this
  set t := tr (support r * sigma)
  have ht_le : t ≤ (P * sigma).trace.re := by
    have e : P * sigma = Pr * sigma + P * (1 - Pr) * P * sigma := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPP, hPPr, hPrP]; simp [Matrix.sub_mul]
    have h1 := tr_mul_psd (one_sub_ind_psd hrH) (conj_psd hsigma P)
    have e2 : (P * (1 - Pr) * P * sigma).trace = ((1 - Pr) * (P * sigma * Pᴴ)).trace := by
      rw [hPh, show P * (1 - Pr) * P * sigma = P * ((1 - Pr) * P * sigma) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    simp only [t, tr, hsupp]
    rw [e, Matrix.trace_add, Complex.add_re, e2]; linarith
  have hPσ : c * (P * sigma).trace.re ≤ 1 := by
    have e : (P * S).trace.re = c * (P * sigma).trace.re := by
      simp only [S, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    linarith
  have ht_le' : t ≤ (2 : ℝ) ^ (-lam) := by
    rw [Real.rpow_neg (by norm_num), ← hc, ← one_div]
    refine ht_le.trans ?_
    rw [le_div_iff₀ hcpos]; linarith
  show (lam : EReal) ≤ -elog t
  rw [EReal.le_neg]
  unfold elog
  split_ifs with htp
  · rw [← EReal.coe_neg]
    refine EReal.coe_le_coe_iff.mpr ?_
    calc Real.logb 2 t ≤ Real.logb 2 ((2 : ℝ) ^ (-lam)) :=
          Real.logb_le_logb_of_le (by norm_num) htp ht_le'
      _ = -lam := Real.logb_rpow (by norm_num) (by norm_num)
  · exact bot_le

/-- upper bound: a large smooth min-entropy forces a nearly full positive part -/
lemma up {rho sigma : Matrix I I ℂ} (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (lam lam' eps : ℝ)
    (h : (lam' : EReal) < traceSmoothMin eps rho sigma) :
    1 - 2 * eps - (2 : ℝ) ^ (lam - lam') ≤ tr (weakPositive (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma) *
      (rho - (((2 : ℝ) ^ lam) : ℂ) • sigma)) := by
  unfold traceSmoothMin at h
  obtain ⟨v, ⟨r, hr, rfl⟩, hv⟩ := lt_sSup_iff.mp h
  rw [two_pow]
  have hS := S_psd hsigma lam
  set c : ℝ := (2 : ℝ) ^ lam with hc
  have hcpos : 0 < c := by positivity
  set S := ((c : ℝ) : ℂ) • sigma
  set X := rho - S
  have hXH : X.IsHermitian := hrho.1.1.sub hS.1
  have hrH : r.IsHermitian := hr.1.1
  obtain ⟨hsupp, -, hPrr⟩ := support_facts hrH
  set Pr := cfc ind r
  have hρ1 : rho.trace.re = 1 := by rw [hrho.2]; simp
  -- overlap bound
  set t := (Pr * sigma).trace.re
  have ht0 : 0 ≤ t := tr_mul_psd (ind_psd r) hsigma
  have ht : t ≤ (2 : ℝ) ^ (-lam') := by
    have hv' : (lam' : EReal) < -elog t := by
      have : dMin r sigma = -elog t := by
        unfold dMin; simp only [t, tr, hsupp]
      rwa [this] at hv
    unfold elog at hv'
    split_ifs at hv' with htp
    · rw [EReal.lt_neg_comm, ← EReal.coe_neg, EReal.coe_lt_coe_iff] at hv'
      have := (Real.logb_lt_iff_lt_rpow (by norm_num) htp).mp hv'
      exact this.le
    · exact (not_lt.mp htp).trans (by positivity)
  have hct : c * t ≤ (2 : ℝ) ^ (lam - lam') := by
    rw [Real.rpow_sub (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
    exact mul_le_mul_of_nonneg_left ht hcpos.le
  -- pairing with the support projector
  have h1 := effect_le (ind_psd r) (one_sub_ind_psd hrH) hXH
  have eX : tr (Pr * X) = (Pr * rho).trace.re - c * t := by
    unfold tr
    simp only [X, S, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul, t]
  -- trace of Pr * rho
  have hY : (r - rho).IsHermitian := hrH.sub hrho.1.1
  have a1 := tr_le_tn (ind_psd r) (one_sub_ind_psd hrH) hY
  have hone : (1 : Matrix I I ℂ).PosSemidef := Matrix.PosSemidef.one
  have hone1 : (1 - (1 : Matrix I I ℂ)).PosSemidef := by rw [sub_self]; exact Matrix.PosSemidef.zero
  have a2 := tr_le_tn hone hone1 (show (-(r - rho)).IsHermitian by rw [neg_sub]; exact hrho.1.1.sub hrH)
  rw [tn_neg, Matrix.one_mul] at a2
  have hn := hr.2.1
  have e1 : tr (Pr * (r - rho)) = r.trace.re - (Pr * rho).trace.re := by
    unfold tr; rw [Matrix.mul_sub, hPrr, Matrix.trace_sub, Complex.sub_re]
  have e2 : tr (-(r - rho)) = 1 - r.trace.re := by
    unfold tr; rw [neg_sub, Matrix.trace_sub, Complex.sub_re, hρ1]
  rw [e1] at a1; rw [e2] at a2
  linarith

end X5T3
end X5mod_T3_Base

section X5mod_T3_Main
open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace X5T3
open X5SM X5SMT X5T2
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable (rho sigma : (k : ℕ) → Matrix (PositiveTensorBasis I k) (PositiveTensorBasis I k) ℂ)

lemma mono : Monotone (minAsymptotic rho sigma) := by
  intro e1 e2 h
  unfold minAsymptotic
  refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (coef_nn k)
  refine sSup_le_sSup ?_
  rintro v ⟨r, ⟨h1, h2, h3⟩, rfl⟩
  exact ⟨r, ⟨h1, h2.trans h, h3⟩, rfl⟩

lemma lb (hrho : ∀ k, QAlgorithms.IsDensityMatrix (rho k))
    (hsigma : ∀ k, (sigma k).PosSemidef) (γ : ℝ)
    (hγ : liminf (spectralMass rho sigma γ) atTop = 1) (eps : ℝ) (heps : 0 < eps) :
    (γ : EReal) ≤ minAsymptotic rho sigma eps := by
  have hb1 : IsBoundedUnder (· ≤ ·) atTop (spectralMass rho sigma γ) :=
    isBoundedUnder_of ⟨1, fun k => mass_le rho sigma hrho hsigma γ k⟩
  have hb0 : IsBoundedUnder (· ≥ ·) atTop (spectralMass rho sigma γ) :=
    isBoundedUnder_of ⟨0, fun k => mass_nn rho sigma hrho hsigma γ k⟩
  have ht : Tendsto (spectralMass rho sigma γ) atTop (𝓝 1) := by
    refine tendsto_of_le_liminf_of_limsup_le hγ.ge ?_ hb1 hb0
    exact limsup_le_of_le hb0.isCoboundedUnder_le
      (Eventually.of_forall fun k => mass_le rho sigma hrho hsigma γ k)
  have hev := (tendsto_order.1 ht).1 (1 - eps ^ 2 / 4) (by
    have : 0 < eps ^ 2 / 4 := by positivity
    linarith)
  unfold minAsymptotic
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hev] with k hk
  have h1 := low (hrho k) (hsigma k) (((k + 1 : ℕ) : ℝ) * γ) eps heps
    (by unfold spectralMass at hk; linarith)
  calc (γ : EReal) = (((1 / ((k + 1 : ℕ) : ℝ)) : ℝ) : EReal) *
        (((((k + 1 : ℕ) : ℝ) * γ) : ℝ) : EReal) := (scale_eq k γ).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (coef_nn k)

lemma geom (γ γ' : ℝ) (h : γ < γ') :
    Tendsto (fun k : ℕ => (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * γ - ((k + 1 : ℕ) : ℝ) * γ')) atTop
      (𝓝 0) := by
  have e : ∀ k : ℕ, (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * γ - ((k + 1 : ℕ) : ℝ) * γ') =
      ((2 : ℝ) ^ (γ - γ')) ^ (k + 1) := by
    intro k
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  simp_rw [e]
  have h0 : 0 ≤ (2 : ℝ) ^ (γ - γ') := by positivity
  have h1 : (2 : ℝ) ^ (γ - γ') < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp (tendsto_add_atTop_nat 1)

lemma ub (hrho : ∀ k, QAlgorithms.IsDensityMatrix (rho k))
    (hsigma : ∀ k, (sigma k).PosSemidef) (γ γ' : ℝ) (hγ : γ < γ')
    (h : ∀ eps : ℝ, 0 < eps → (γ' : EReal) < minAsymptotic rho sigma eps) :
    liminf (spectralMass rho sigma γ) atTop = 1 := by
  refine Tendsto.liminf_eq ?_
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · set η := 1 - a
    have hη : 0 < η := by simp only [η]; linarith
    have hev := eventually_lt_of_lt_liminf (h (η / 4) (by positivity))
    have hg := (tendsto_order.1 (geom γ γ' hγ)).2 (η / 2) (by positivity)
    filter_upwards [hev, hg] with k hk hgk
    have hk' : ((((k + 1 : ℕ) : ℝ) * γ' : ℝ) : EReal) < traceSmoothMin (η / 4) (rho k) (sigma k) := by
      by_contra hc
      push_neg at hc
      have := mul_le_mul_of_nonneg_left hc (coef_nn k)
      rw [scale_eq] at this
      exact absurd hk (not_lt.mpr this)
    have := up (hrho k) (hsigma k) (((k + 1 : ℕ) : ℝ) * γ) (((k + 1 : ℕ) : ℝ) * γ') (η / 4) hk'
    unfold spectralMass
    simp only [η] at this hgk ⊢
    linarith
  · exact Eventually.of_forall fun k => lt_of_le_of_lt (mass_le rho sigma hrho hsigma γ k) ha

theorem main (hrho : ∀ k, QAlgorithms.IsDensityMatrix (rho k))
    (hsigma : ∀ k, (sigma k).PosSemidef) :
    Tendsto (minAsymptotic rho sigma) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (spectralInf rho sigma)) := by
  have ht := (mono rho sigma).tendsto_nhdsGT 0
  convert ht using 2
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    rintro _ ⟨eps, heps, rfl⟩
    refine sSup_le ?_
    rintro _ ⟨γ, rfl, hγ⟩
    exact lb rho sigma hrho hsigma γ hγ eps heps
  · by_contra hc
    push_neg at hc
    obtain ⟨γ, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    obtain ⟨γ', h3, h4⟩ := EReal.lt_iff_exists_real_btwn.mp h2
    have hγ : γ < γ' := EReal.coe_lt_coe_iff.mp h3
    have hmem : liminf (spectralMass rho sigma γ) atTop = 1 :=
      ub rho sigma hrho hsigma γ γ' hγ fun eps heps =>
        lt_of_lt_of_le h4 (sInf_le (Set.mem_image_of_mem (minAsymptotic rho sigma)
          (show eps ∈ Set.Ioi (0 : ℝ) from heps)))
    have : (γ : EReal) ≤ spectralInf rho sigma := le_sSup ⟨γ, rfl, hmem⟩
    exact absurd h1 (not_lt.mpr this)

end X5T3
end X5mod_T3_Main


noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support50.P21
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

section Statements

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Nonempty I] [Nonempty J]

theorem solution (rho sigma : (k : ℕ) → Mat (PositiveTensorBasis I k))
    (hrho : ∀ k, IsDensityMatrix (rho k)) (hsigma : ∀ k, (sigma k).PosSemidef) :
    Tendsto (minAsymptotic rho sigma) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (spectralInf rho sigma)) :=
  X5T3.main rho sigma hrho hsigma

end Statements

end

