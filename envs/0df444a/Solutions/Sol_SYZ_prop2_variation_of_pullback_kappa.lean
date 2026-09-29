-- Prove2me | solution 1 for SYZ.prop2_variation_of_pullback_kappa
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T16:15:22.072671+00:00
-- url     : https://prove2.me/submissions/9f12fc81-ddea-4b34-9b3b-449e1916b63e

import Mathlib
import Definitions.Def_syz_flat_model

/-! Disproof of dc343d6f SYZ.prop2_variation_of_pullback_kappa (unoriented form).
Counterexample: n = 1, F s x = (-1 + i s) x · e₁ at t = 0.
* F 0 x = -x e₁ is special Lagrangian (ω vanishes on a line, κ = Im(-1) = 0) and immersed (g = 1).
* LHS: κ(∂F(s,x)) = Im(-1 + i s) = s, so d/ds at 0 is 1.
* RHS: θ(y) = ω(i y e₁, -e₁) = y, √g = 1, g⁻¹ = 1, so -∂_y(y) = -1.
1 ≠ -1.  (The oriented statement, with Re Ω > 0, excludes this example: Re Ω = -1 here.) -/

set_option autoImplicit false

open SYZ Complex

namespace SYZDP

noncomputable def e1 : Amb 1 := EuclideanSpace.single 0 1
noncomputable def cF (s : ℝ) : ℂ := -1 + (s : ℂ) * I
noncomputable def P : Dom 1 →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 1))
noncomputable def Fx (s : ℝ) (x : Dom 1) : Amb 1 := (cF s * ((x 0 : ℝ) : ℂ)) • e1

lemma P_apply (x : Dom 1) : P x = ((x 0 : ℝ) : ℂ) := rfl

lemma hasFDerivAt_Fx (s : ℝ) (x : Dom 1) :
    HasFDerivAt (Fx s) ((cF s • P).smulRight e1) x := by
  have h1 : HasFDerivAt (fun y : Dom 1 => cF s * P y) (cF s • P) x :=
    P.hasFDerivAt.const_mul (cF s)
  have h2 := h1.smul_const e1
  exact h2

lemma D_Fx (s : ℝ) (x : Dom 1) (i : Fin 1) : D (Fx s) i x = cF s • e1 := by
  unfold D
  rw [(hasFDerivAt_Fx s x).fderiv]
  fin_cases i
  simp [P_apply, basis]

lemma hasDerivAt_Fx (y : Dom 1) (t : ℝ) :
    HasDerivAt (fun s => Fx s y) ((I * ((y 0 : ℝ) : ℂ)) • e1) t := by
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h1 : HasDerivAt cF I t := by
    have := (h0.mul_const I).const_add (-1)
    rw [one_mul] at this
    exact this
  exact (h1.mul_const ((y 0 : ℝ) : ℂ)).smul_const e1

lemma smooth_Fx : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom 1 => Fx p.1 p.2) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom 1 => cF p.1) := by
    have : (fun p : ℝ × Dom 1 => cF p.1) =
        fun p => (-1 : ℂ) + Complex.ofRealCLM p.1 * I := by
      funext p; rfl
    rw [this]
    exact contDiff_const.add ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const)
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom 1 => P p.2) := P.contDiff.comp contDiff_snd
  exact (hc.mul hx).smul contDiff_const


lemma e1_apply : e1 0 = 1 := by simp [e1]

lemma inner_e1 (a b : ℂ) : inner ℂ (a • e1) (b • e1) = (starRingEnd ℂ) a * b := by
  rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [e1]

lemma kappa_Fx (s : ℝ) (x : Dom 1) : kappa (fun i => D (Fx s) i x) = s := by
  simp only [D_Fx]
  unfold kappa hVol
  rw [Matrix.det_unique]
  simp [e1_apply, cF]

lemma deriv_Fx (y : Dom 1) (t : ℝ) :
    deriv (fun s => Fx s y) t = (I * ((y 0 : ℝ) : ℂ)) • e1 := (hasDerivAt_Fx y t).deriv

lemma theta_Fx (y : Dom 1) (j : Fin 1) : theta1 Fx 0 y j = y 0 := by
  unfold theta1 kForm
  rw [deriv_Fx, D_Fx, inner_e1]
  simp [cF]

lemma gInd_Fx (y : Dom 1) : gInd (Fx 0) y = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp only [gInd, gAmb, Matrix.of_apply, D_Fx, inner_e1]
  simp [cF]

lemma slag_Fx (y : Dom 1) : IsSpecialLagrangianAt (Fx 0) y := by
  refine ⟨fun i j => ?_, ?_⟩
  · unfold kForm
    rw [D_Fx, D_Fx, inner_e1]
    simp [cF]
  · rw [kappa_Fx]

lemma lhs_Fx (x : Dom 1) : deriv (fun s => kappa (fun i => D (Fx s) i x)) 0 = 1 := by
  simp only [kappa_Fx]
  exact deriv_id 0

lemma rhs_Fx (x : Dom 1) :
    -∑ i, D (fun y => volDens (Fx 0) y
          * ∑ j, (gInd (Fx 0) y)⁻¹ i j * theta1 Fx 0 y j) i x = -1 := by
  have hf : (fun y => volDens (Fx 0) y
          * ∑ j, (gInd (Fx 0) y)⁻¹ (0 : Fin 1) j * theta1 Fx 0 y j) =
        fun y => (EuclideanSpace.proj (0 : Fin 1) : Dom 1 →L[ℝ] ℝ) y := by
    funext y
    simp [volDens, gInd_Fx, theta_Fx]
  rw [Fin.sum_univ_one, hf]
  unfold D
  rw [ContinuousLinearMap.fderiv]
  simp [basis]

end SYZDP

open SYZ in
theorem solution : ¬ (∀ {n : ℕ} (F : ℝ → Dom n → Amb n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (hSL : ∀ y, IsSpecialLagrangianAt (F t) y)
    (him : ∀ y, (gInd (F t) y).det ≠ 0) (x : Dom n),
    deriv (fun s => kappa (fun i => D (F s) i x)) t
      = -∑ i, D (fun y => volDens (F t) y
          * ∑ j, (gInd (F t) y)⁻¹ i j * theta1 F t y j) i x) := by
  intro h
  have := h SYZDP.Fx SYZDP.smooth_Fx 0 SYZDP.slag_Fx
    (fun y => by rw [SYZDP.gInd_Fx]; simp) 0
  rw [SYZDP.lhs_Fx, SYZDP.rhs_Fx] at this
  norm_num at this
