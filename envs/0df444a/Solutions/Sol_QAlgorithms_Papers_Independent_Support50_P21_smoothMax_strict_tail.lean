-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P21.smoothMax_strict_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T23:48:01.465822+00:00
-- url     : https://prove2.me/submissions/532afd83-ea78-4da0-956c-8cc8f74bb142

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

section X5mod_SM_L15
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace X5SMT
open X5SM
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (Le traceSmoothMax traceSmoothingBall strictPositive)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem main15 (rho sigma : Matrix I I ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hsigma : QAlgorithms.IsDensityMatrix sigma) (lambda : ℝ) :
    traceSmoothMax (Real.sqrt (8 * tr (strictPositive
      (rho - (((2 : ℝ) ^ lambda) : ℂ) • sigma) * rho))) rho sigma ≤
      (lambda : EReal) := by
  rw [two_pow]
  set S := (((2 : ℝ) ^ lambda : ℝ) : ℂ) • sigma
  have hS : S.PosSemidef := hsigma.1.smul (by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ lambda := by positivity
    exact_mod_cast this)
  set X := rho - S
  have hX : IsSelfAdjoint X := (hrho.1.1.sub hS.1).isSelfAdjoint
  set P := strictPositive X
  set Δ := cfc (fun x : ℝ => max x 0) X
  have hPX : P * X = Δ := by
    have e : P * X = cfc (fun x : ℝ => (if 0 < x then (1 : ℝ) else 0) * x) X := by
      rw [cfc_mul _ _ _ (fin _ _) (fin _ _), cfc_id' ℝ X hX]; rfl
    rw [e]
    refine cfc_congr fun x _ => ?_
    split_ifs with h
    · rw [one_mul, max_eq_left h.le]
    · rw [zero_mul, max_eq_right (not_lt.mp h)]
  have hΔ : Δ.PosSemidef := (cfc_nonneg (fun x _ => le_max_right x 0) : 0 ≤ Δ).posSemidef
  have hP : P.PosSemidef := (cfc_nonneg (fun x _ => by split_ifs <;> norm_num) :
    0 ≤ cfc (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) X).posSemidef
  have hdom : Le rho ((((2 : ℝ) ^ lambda) : ℂ) • sigma + Δ) := by
    unfold Le; rw [two_pow]
    have e : S + Δ - rho = cfc (fun x : ℝ => max x 0 - x) X := by
      rw [cfc_sub _ _ _ (fin _ _) (fin _ _), cfc_id' ℝ X hX]; simp only [X, Δ]; abel
    rw [e]
    exact (cfc_nonneg (fun x _ => by simp only [sub_nonneg]; exact le_max_left x 0) :
      0 ≤ cfc (fun x : ℝ => max x 0 - x) X).posSemidef
  have htr : tr Δ ≤ tr (P * rho) := by
    unfold tr
    rw [← hPX]
    have := tr_mul_psd hP hS
    simp only [X, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    linarith
  exact main rho sigma Δ hrho hsigma hΔ lambda _ hdom (Real.sqrt_le_sqrt (by linarith))

end X5SMT
end X5mod_SM_L15

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

theorem solution (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (lambda : ℝ) :
    traceSmoothMax (Real.sqrt (8 * tr (strictPositive
      (rho - (((2 : ℝ) ^ lambda) : ℂ) • sigma) * rho))) rho sigma ≤
      (lambda : EReal) :=
  X5SMT.main15 rho sigma hrho hsigma lambda

end Statements

end

