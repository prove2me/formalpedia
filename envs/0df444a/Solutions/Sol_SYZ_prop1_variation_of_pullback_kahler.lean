-- Prove2me | solution 1 for SYZ.prop1_variation_of_pullback_kahler
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T16:10:30.851993+00:00
-- url     : https://prove2.me/submissions/4678f172-e9a9-4dc9-b376-0d3ade188b32

import Mathlib
import Definitions.Def_syz_flat_model

/-! a79c96ca SYZ.prop1_variation_of_pullback_kahler (Strominger–Yau–Zaslow 1996, Section 3, Prop. 1).
With Φ(t,x) = F t x on ℝ × ℝⁿ and D² := fderiv (fderiv Φ):
* ∂_t ω(∂_iF, ∂_jF) = ω(D²(∂_t,∂_i), ∂_jF) + ω(∂_iF, D²(∂_t,∂_j))  (product rule for Im⟪·,·⟫);
* ∂_i θ_j = ω(D²(∂_i,∂_t), ∂_jF) + ω(∂_tF, D²(∂_i,∂_j)), and symmetrically for ∂_j θ_i;
* symmetry of second derivatives cancels the ω(∂_tF, D²(∂_i,∂_j)) terms, and ω(u,v) = -ω(v,u)
  matches the rest.  No Lagrangian hypothesis is needed.
No `Theorems.*` module is imported. -/

set_option autoImplicit false

namespace SYZP

open SYZ Function

variable {n : ℕ}

/-- the `x`-direction `j` and the `t`-direction in `ℝ × Dom n` -/
noncomputable def vx (n : ℕ) (j : Fin n) : ℝ × Dom n := (0, basis j)
noncomputable def vt (n : ℕ) : ℝ × Dom n := (1, 0)

lemma D_right' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Dom n → V)
    (t : ℝ) (x : Dom n) (hd : DifferentiableAt ℝ h (t, x)) (j : Fin n) :
    D (fun y => h (t, y)) j x = fderiv ℝ h (t, x) (vx n j) := by
  have H : HasFDerivAt (fun y => h (t, y))
      ((fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Dom n))) x :=
    hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  unfold D
  rw [H.fderiv]
  rfl

lemma deriv_left' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Dom n → V)
    (t : ℝ) (x : Dom n) (hd : DifferentiableAt ℝ h (t, x)) :
    deriv (fun s => h (s, x)) t = fderiv ℝ h (t, x) (vt n) := by
  have H : HasFDerivAt (fun s => h (s, x))
      ((fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inl ℝ ℝ (Dom n))) t :=
    hd.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)
  rw [H.hasDerivAt.deriv]
  rfl

/-- the family as a map on `ℝ × Dom n` -/
noncomputable def Phi (F : ℝ → Dom n → Amb n) : ℝ × Dom n → Amb n := fun p => F p.1 p.2

lemma DF_eq (F : ℝ → Dom n → Amb n) (hd : Differentiable ℝ (Phi F)) (s : ℝ) (x : Dom n)
    (j : Fin n) : D (F s) j x = fderiv ℝ (Phi F) (s, x) (vx n j) :=
  D_right' (Phi F) s x (hd _) j

lemma Dt_eq (F : ℝ → Dom n → Amb n) (hd : Differentiable ℝ (Phi F)) (t : ℝ) (x : Dom n) :
    deriv (fun s => F s x) t = fderiv ℝ (Phi F) (t, x) (vt n) :=
  deriv_left' (Phi F) t x (hd _)

lemma kForm_anti (u v : Amb n) : kForm u v = -kForm v u := by
  unfold kForm
  rw [← inner_conj_symm, Complex.conj_im]

lemma hasFDerivAt_col {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P → Amb n) (hΦ : ContDiff ℝ 2 Φ) (u p : P) :
    HasFDerivAt (fun q => fderiv ℝ Φ q u) ((fderiv ℝ (fderiv ℝ Φ) p).flip u) p := by
  have hd : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have := (hd p).hasFDerivAt.clm_apply (hasFDerivAt_const u p)
  simpa using this

/-- `ω(DΦ·u, DΦ·v)` as a function on the parameter space -/
noncomputable def kF {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P → Amb n) (u v : P) : P → ℝ :=
  fun q => kForm (fderiv ℝ Φ q u) (fderiv ℝ Φ q v)

lemma hasFDerivAt_kF {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P → Amb n) (hΦ : ContDiff ℝ 2 Φ) (u v p : P) :
    HasFDerivAt (kF Φ u v) (Complex.imCLM.comp ((fderivInnerCLM ℂ
      (fderiv ℝ Φ p u, fderiv ℝ Φ p v)).comp
        (((fderiv ℝ (fderiv ℝ Φ) p).flip u).prod ((fderiv ℝ (fderiv ℝ Φ) p).flip v)))) p :=
  Complex.imCLM.hasFDerivAt.comp p
    ((hasFDerivAt_col Φ hΦ u p).inner ℂ (hasFDerivAt_col Φ hΦ v p))

lemma fderiv_kF {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P → Amb n) (hΦ : ContDiff ℝ 2 Φ) (u v p w : P) :
    fderiv ℝ (kF Φ u v) p w =
      kForm (fderiv ℝ (fderiv ℝ Φ) p w u) (fderiv ℝ Φ p v) +
        kForm (fderiv ℝ Φ p u) (fderiv ℝ (fderiv ℝ Φ) p w v) := by
  rw [(hasFDerivAt_kF Φ hΦ u v p).fderiv]
  simp [fderivInnerCLM_apply, kForm]
  ring

theorem prop1_lib (F : ℝ → Dom n → Amb n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (x : Dom n) (i j : Fin n) :
    deriv (fun s => kForm (D (F s) i x) (D (F s) j x)) t
      = D (fun y => theta1 F t y j) i x - D (fun y => theta1 F t y i) j x := by
  have hΦ : ContDiff ℝ 2 (Phi F) :=
    hF.of_le (by first | simp | exact WithTop.coe_le_coe.2 le_top)
  have hd : Differentiable ℝ (Phi F) := hΦ.differentiable (by norm_num)
  have hkd : ∀ u v, Differentiable ℝ (kF (Phi F) u v) :=
    fun u v p => (hasFDerivAt_kF (Phi F) hΦ u v p).differentiableAt
  have hL : (fun s => kForm (D (F s) i x) (D (F s) j x)) =
      fun s => kF (Phi F) (vx n i) (vx n j) (s, x) := by
    funext s; rw [DF_eq F hd, DF_eq F hd]; rfl
  have hθ : ∀ k, (fun y => theta1 F t y k) = fun y => kF (Phi F) (vt n) (vx n k) (t, y) := by
    intro k; funext y; unfold theta1; rw [Dt_eq F hd, DF_eq F hd]; rfl
  rw [hL, hθ, hθ, deriv_left' _ t x (hkd _ _ _), D_right' _ t x (hkd _ _ _),
    D_right' _ t x (hkd _ _ _), fderiv_kF _ hΦ, fderiv_kF _ hΦ, fderiv_kF _ hΦ]
  have hs : ∀ v w, fderiv ℝ (fderiv ℝ (Phi F)) (t, x) v w =
      fderiv ℝ (fderiv ℝ (Phi F)) (t, x) w v :=
    hΦ.contDiffAt.isSymmSndFDerivAt (by simp)
  rw [hs (vx n i) (vt n), hs (vx n j) (vt n), hs (vx n j) (vx n i),
    kForm_anti (fderiv ℝ (fderiv ℝ (Phi F)) (t, x) (vt n) (vx n j))]
  ring

end SYZP

open SYZ in
theorem solution {n : ℕ} (F : ℝ → Dom n → Amb n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (x : Dom n) (i j : Fin n) :
    deriv (fun s => kForm (D (F s) i x) (D (F s) j x)) t
      = D (fun y => theta1 F t y j) i x - D (fun y => theta1 F t y i) j x := by
  exact SYZP.prop1_lib F hF t x i j
