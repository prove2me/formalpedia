-- Prove2me | solution 1 for RaritaSchwinger.massive_constraints
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:46:27.701956+00:00
-- url     : https://prove2.me/submissions/2988facd-f14f-4445-9545-bb7d8c6997f1

import Mathlib
import Definitions.Def_RaritaSchwinger_core

set_option autoImplicit false

open DiracEquation RaritaSchwinger Matrix

namespace RS69

/-! ### Gamma-matrix algebra -/

variable {g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}

lemma anti (hg : IsGammaFamily g) {i j : Fin 4} (h : i ≠ j) : g i * g j = -(g j * g i) := by
  have := hg i j
  simp [eta, h] at this
  exact eq_neg_of_add_eq_zero_left this

lemma anti' (hg : IsGammaFamily g) {i j : Fin 4} (h : i ≠ j) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    g i * (g j * X) = -(g j * (g i * X)) := by
  rw [← mul_assoc, anti hg h, neg_mul, mul_assoc]

lemma sq (hg : IsGammaFamily g) (i : Fin 4) :
    g i * g i = eta i i • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h := hg i i
  have h2 : (2:ℂ) • (g i * g i) = (2:ℂ) • (eta i i • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    rw [two_smul, h, smul_smul]
  exact smul_right_injective _ (two_ne_zero) h2

lemma sq' (hg : IsGammaFamily g) (i : Fin 4) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    g i * (g i * X) = eta i i • X := by
  rw [← mul_assoc, sq hg i, smul_mul, one_mul]

lemma sigma_eq (hg : IsGammaFamily g) (mu nu : Fin 4) :
    sigma g mu nu = Complex.I • (g mu * g nu) - (Complex.I * eta mu nu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h : g nu * g mu = (2 * eta mu nu) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - g mu * g nu := by
    rw [← hg mu nu]; abel
  rw [sigma, h]
  module

/-! ### Levi-Civita values -/

lemma levi_rep01 (a c d : Fin 4) : levi a a c d = 0 := by
  unfold levi; exact Matrix.det_zero_of_row_eq (i := 0) (j := 1) (by decide) rfl
lemma levi_rep02 (a b d : Fin 4) : levi a b a d = 0 := by
  unfold levi; exact Matrix.det_zero_of_row_eq (i := 0) (j := 2) (by decide) rfl
lemma levi_rep03 (a b c : Fin 4) : levi a b c a = 0 := by
  unfold levi; exact Matrix.det_zero_of_row_eq (i := 0) (j := 3) (by decide) rfl
lemma levi_rep12 (a b d : Fin 4) : levi a b b d = 0 := by
  unfold levi; exact Matrix.det_zero_of_row_eq (i := 1) (j := 2) (by decide) rfl
lemma levi_rep13 (a b c : Fin 4) : levi a b c b = 0 := by
  unfold levi; exact Matrix.det_zero_of_row_eq (i := 1) (j := 3) (by decide) rfl
lemma levi_rep23 (a b c : Fin 4) : levi a b c c = 0 := by
  unfold levi; exact Matrix.det_zero_of_row_eq (i := 2) (j := 3) (by decide) rfl

lemma levi_swap02 (a b c d : Fin 4) : levi c b a d = -levi a b c d := by
  unfold levi
  have : Matrix.of ![(Pi.single c 1 : Fin 4 → ℂ), Pi.single b 1, Pi.single a 1, Pi.single d 1] =
      (Matrix.of ![(Pi.single a 1 : Fin 4 → ℂ), Pi.single b 1, Pi.single c 1,
        Pi.single d 1]).submatrix (Equiv.swap 0 2) id := by
    ext i j; fin_cases i <;> rfl
  rw [this, Matrix.det_permute]
  simp [Equiv.Perm.sign_swap]

lemma levi_0123 : levi 0 1 2 3 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_0132 : levi 0 1 3 2 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_0213 : levi 0 2 1 3 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_0231 : levi 0 2 3 1 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_0312 : levi 0 3 1 2 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_0321 : levi 0 3 2 1 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_1023 : levi 1 0 2 3 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_1032 : levi 1 0 3 2 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_1203 : levi 1 2 0 3 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_1230 : levi 1 2 3 0 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_1302 : levi 1 3 0 2 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_1320 : levi 1 3 2 0 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_2013 : levi 2 0 1 3 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_2031 : levi 2 0 3 1 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_2103 : levi 2 1 0 3 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_2130 : levi 2 1 3 0 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_2301 : levi 2 3 0 1 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_2310 : levi 2 3 1 0 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_3012 : levi 3 0 1 2 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_3021 : levi 3 0 2 1 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_3102 : levi 3 1 0 2 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_3120 : levi 3 1 2 0 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_3201 : levi 3 2 0 1 = -1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma levi_3210 : levi 3 2 1 0 = 1 := by
  simp [levi, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove] <;> norm_num

lemma I2 (hg : IsGammaFamily g) (nu : Fin 4) :
    ∑ mu, gammaLower g mu * sigma g mu nu = (3 * Complex.I) • g nu := by
  have a10 := anti' hg (show (1:Fin 4) ≠ 0 by decide)
  have a20 := anti' hg (show (2:Fin 4) ≠ 0 by decide)
  have a30 := anti' hg (show (3:Fin 4) ≠ 0 by decide)
  have a21 := anti' hg (show (2:Fin 4) ≠ 1 by decide)
  have a31 := anti' hg (show (3:Fin 4) ≠ 1 by decide)
  have a32 := anti' hg (show (3:Fin 4) ≠ 2 by decide)
  have b10 := anti hg (show (1:Fin 4) ≠ 0 by decide)
  have b20 := anti hg (show (2:Fin 4) ≠ 0 by decide)
  have b30 := anti hg (show (3:Fin 4) ≠ 0 by decide)
  have b21 := anti hg (show (2:Fin 4) ≠ 1 by decide)
  have b31 := anti hg (show (3:Fin 4) ≠ 1 by decide)
  have b32 := anti hg (show (3:Fin 4) ≠ 2 by decide)
  have s0 := sq hg 0
  have s1 := sq hg 1
  have s2 := sq hg 2
  have s3 := sq hg 3
  have t0 := sq' hg 0
  have t1 := sq' hg 1
  have t2 := sq' hg 2
  have t3 := sq' hg 3
  simp only [eta] at s0 s1 s2 s3 t0 t1 t2 t3
  norm_num at s0 s1 s2 s3 t0 t1 t2 t3
  fin_cases nu <;>
  simp [Fin.sum_univ_four, gammaLower, sigma, eta, mul_sub, smul_mul, mul_smul, mul_assoc,
    a10, a20, a30, a21, a31, a32, b10, b20, b30, b21, b31, b32, s0, s1, s2, s3, t0, t1, t2, t3,
    smul_sub, smul_neg, neg_smul] <;> module

set_option maxHeartbeats 4000000 in
lemma I1 (hg : IsGammaFamily g) (rho nu : Fin 4) :
    ∑ mu, ∑ kappa, levi mu kappa rho nu • (gammaLower g mu * (gamma5 g * gammaLower g kappa))
      = (-2 : ℂ) • sigma g rho nu := by
  have a10 := anti' hg (show (1:Fin 4) ≠ 0 by decide)
  have a20 := anti' hg (show (2:Fin 4) ≠ 0 by decide)
  have a30 := anti' hg (show (3:Fin 4) ≠ 0 by decide)
  have a21 := anti' hg (show (2:Fin 4) ≠ 1 by decide)
  have a31 := anti' hg (show (3:Fin 4) ≠ 1 by decide)
  have a32 := anti' hg (show (3:Fin 4) ≠ 2 by decide)
  have b10 := anti hg (show (1:Fin 4) ≠ 0 by decide)
  have b20 := anti hg (show (2:Fin 4) ≠ 0 by decide)
  have b30 := anti hg (show (3:Fin 4) ≠ 0 by decide)
  have b21 := anti hg (show (2:Fin 4) ≠ 1 by decide)
  have b31 := anti hg (show (3:Fin 4) ≠ 1 by decide)
  have b32 := anti hg (show (3:Fin 4) ≠ 2 by decide)
  have s0 : g 0 * g 0 = 1 := by rw [sq hg]; simp [eta]
  have s1 : g 1 * g 1 = -1 := by rw [sq hg]; simp [eta]
  have s2 : g 2 * g 2 = -1 := by rw [sq hg]; simp [eta, show (2:Fin 4) ≠ 0 by decide]
  have s3 : g 3 * g 3 = -1 := by rw [sq hg]; simp [eta, show (3:Fin 4) ≠ 0 by decide]
  have t0 : ∀ X : Matrix (Fin 4) (Fin 4) ℂ, g 0 * (g 0 * X) = X := by
    intro X; rw [sq' hg]; simp [eta]
  have t1 : ∀ X : Matrix (Fin 4) (Fin 4) ℂ, g 1 * (g 1 * X) = -X := by
    intro X; rw [sq' hg]; simp [eta]
  have t2 : ∀ X : Matrix (Fin 4) (Fin 4) ℂ, g 2 * (g 2 * X) = -X := by
    intro X; rw [sq' hg]; simp [eta, show (2:Fin 4) ≠ 0 by decide]
  have t3 : ∀ X : Matrix (Fin 4) (Fin 4) ℂ, g 3 * (g 3 * X) = -X := by
    intro X; rw [sq' hg]; simp [eta, show (3:Fin 4) ≠ 0 by decide]
  fin_cases rho <;> fin_cases nu <;>
  simp only [Fin.sum_univ_four, Fin.isValue, levi_rep01, levi_rep02, levi_rep03, levi_rep12,
    levi_rep13, levi_rep23, zero_smul, add_zero, zero_add, Fin.zero_eta, Fin.mk_one] <;>
  simp [levi_rep01, levi_rep02, levi_rep03, levi_rep12, levi_rep13, levi_rep23, levi_0123, levi_0132, levi_0213, levi_0231, levi_0312, levi_0321, levi_1023, levi_1032, levi_1203, levi_1230, levi_1302, levi_1320, levi_2013, levi_2031, levi_2103, levi_2130, levi_2301, levi_2310, levi_3012, levi_3021, levi_3102, levi_3120, levi_3201, levi_3210, gammaLower, gamma5, sigma, eta, mul_sub, smul_mul, mul_smul, mul_assoc,
    a10, a20, a30, a21, a31, a32, b10, b20, b30, b21, b31, b32, s0, s1, s2, s3, t0, t1, t2, t3,
    smul_sub, smul_neg, neg_smul] <;> module

/-! ### Calculus helpers -/

noncomputable def mvL (M : Matrix (Fin 4) (Fin 4) ℂ) : (Fin 4 → ℂ) →L[ℝ] (Fin 4 → ℂ) :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin M).restrictScalars ℝ)

lemma mvL_apply (M : Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → ℂ) : mvL M v = M *ᵥ v := rfl

lemma diff_mulVec (M : Matrix (Fin 4) (Fin 4) ℂ) {f : (Fin 4 → ℝ) → (Fin 4 → ℂ)} {x : Fin 4 → ℝ}
    (hf : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun y => M *ᵥ f y) x :=
  (mvL M).differentiableAt.comp x hf

lemma pd_mulVec (M : Matrix (Fin 4) (Fin 4) ℂ) {f : (Fin 4 → ℝ) → (Fin 4 → ℂ)} {x : Fin 4 → ℝ}
    (hf : DifferentiableAt ℝ f x) (mu : Fin 4) :
    pd (fun y => M *ᵥ f y) mu x = M *ᵥ pd f mu x := by
  unfold pd
  have h := ((mvL M).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  change fderiv ℝ ((mvL M) ∘ f) x _ = _
  rw [h]; rfl

lemma pd_sum {ι : Type} (s : Finset ι) (F : ι → (Fin 4 → ℝ) → (Fin 4 → ℂ)) {x : Fin 4 → ℝ}
    (hF : ∀ i, DifferentiableAt ℝ (F i) x) (mu : Fin 4) :
    pd (fun y => ∑ i ∈ s, F i y) mu x = ∑ i ∈ s, pd (F i) mu x := by
  unfold pd; rw [fderiv_fun_sum (fun i _ => hF i)]; simp

lemma pd_sub {F G : (Fin 4 → ℝ) → (Fin 4 → ℂ)} {x : Fin 4 → ℝ} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (mu : Fin 4) :
    pd (fun y => F y - G y) mu x = pd F mu x - pd G mu x := by
  unfold pd; rw [fderiv_fun_sub hF hG]; rfl

lemma pd_smul (c : ℂ) {F : (Fin 4 → ℝ) → (Fin 4 → ℂ)} {x : Fin 4 → ℝ}
    (hF : DifferentiableAt ℝ F x) (mu : Fin 4) :
    pd (fun y => c • F y) mu x = c • pd F mu x := by
  unfold pd; rw [fderiv_fun_const_smul hF c]; rfl

lemma pd_zero (x : Fin 4 → ℝ) (mu : Fin 4) : pd (fun _ => (0 : Fin 4 → ℂ)) mu x = 0 := by
  unfold pd; simp

lemma diff_pd {f : (Fin 4 → ℝ) → (Fin 4 → ℂ)} (hf : ContDiff ℝ 2 f) (rho : Fin 4) (x : Fin 4 → ℝ) :
    DifferentiableAt ℝ (fun y => pd f rho y) x := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  unfold pd
  exact (hd x).clm_apply (differentiableAt_const _)

lemma pd2_symm {f : (Fin 4 → ℝ) → (Fin 4 → ℂ)} (hf : ContDiff ℝ 2 f) (a b : Fin 4)
    (x : Fin 4 → ℝ) :
    pd (fun y => pd f a y) b x = pd (fun y => pd f b y) a x := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hs : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  unfold pd
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _),
    fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simpa using hs (Pi.single b 1) (Pi.single a 1)

lemma pd_eq (L : Fin 4 → Fin 4 → Fin 4 → ℂ) (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ)
    (S : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (f : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℂ))
    (x : Fin 4 → ℝ) (hd0 : ∀ nu, DifferentiableAt ℝ (f nu) x)
    (hd1 : ∀ nu rho, DifferentiableAt ℝ (fun y => pd (f nu) rho y) x) (mu : Fin 4) :
    pd (fun y => (∑ kappa, ∑ rho, ∑ nu, L kappa rho nu • (A kappa) *ᵥ pd (f nu) rho y)
        - c • ∑ nu, S nu *ᵥ f nu y) mu x =
      (∑ kappa, ∑ rho, ∑ nu, L kappa rho nu • (A kappa) *ᵥ pd (fun y => pd (f nu) rho y) mu x)
        - c • ∑ nu, S nu *ᵥ pd (f nu) mu x := by
  have dA : ∀ kappa rho nu, DifferentiableAt ℝ
      (fun y => L kappa rho nu • (A kappa) *ᵥ pd (f nu) rho y) x :=
    fun kappa rho nu => (diff_mulVec _ (hd1 nu rho)).fun_const_smul _
  have dB : ∀ nu, DifferentiableAt ℝ (fun y => S nu *ᵥ f nu y) x :=
    fun nu => diff_mulVec _ (hd0 nu)
  have dA2 : ∀ kappa rho, DifferentiableAt ℝ
      (fun y => ∑ nu, L kappa rho nu • (A kappa) *ᵥ pd (f nu) rho y) x :=
    fun kappa rho => DifferentiableAt.fun_sum fun nu _ => dA kappa rho nu
  have dA3 : ∀ kappa, DifferentiableAt ℝ
      (fun y => ∑ rho, ∑ nu, L kappa rho nu • (A kappa) *ᵥ pd (f nu) rho y) x :=
    fun kappa => DifferentiableAt.fun_sum fun rho _ => dA2 kappa rho
  have dA4 : DifferentiableAt ℝ
      (fun y => ∑ kappa, ∑ rho, ∑ nu, L kappa rho nu • (A kappa) *ᵥ pd (f nu) rho y) x :=
    DifferentiableAt.fun_sum fun kappa _ => dA3 kappa
  have dB2 : DifferentiableAt ℝ (fun y => ∑ nu, S nu *ᵥ f nu y) x :=
    DifferentiableAt.fun_sum fun nu _ => dB nu
  rw [pd_sub dA4 (dB2.fun_const_smul c), pd_smul c dB2,
    pd_sum Finset.univ (fun nu y => S nu *ᵥ f nu y) dB,
    pd_sum Finset.univ (fun kappa y => ∑ rho, ∑ nu, L kappa rho nu • (A kappa) *ᵥ pd (f nu) rho y) dA3]
  congr 1
  · refine Finset.sum_congr rfl fun kappa _ => ?_
    rw [pd_sum Finset.univ (fun rho y => ∑ nu, L kappa rho nu • (A kappa) *ᵥ pd (f nu) rho y)
      (dA2 kappa)]
    refine Finset.sum_congr rfl fun rho _ => ?_
    rw [pd_sum Finset.univ (fun nu y => L kappa rho nu • (A kappa) *ᵥ pd (f nu) rho y)
      (dA kappa rho)]
    refine Finset.sum_congr rfl fun nu _ => ?_
    rw [pd_smul _ (diff_mulVec _ (hd1 nu rho)), pd_mulVec _ (hd1 nu rho)]
  · congr 1
    exact Finset.sum_congr rfl fun nu _ => pd_mulVec _ (hd0 nu) mu

/-! ### Sum manipulations -/

lemma reorder3 {V : Type} [AddCommMonoid V] (H : Fin 4 → Fin 4 → Fin 4 → V) :
    ∑ a, ∑ b, ∑ c, H a b c = ∑ c, ∑ b, ∑ a, H a b c := by
  calc ∑ a, ∑ b, ∑ c, H a b c = ∑ b, ∑ a, ∑ c, H a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, H a b c := Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, H a b c := Finset.sum_comm

lemma reorder4 {V : Type} [AddCommMonoid V] (H : Fin 4 → Fin 4 → Fin 4 → Fin 4 → V) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b c d = ∑ c, ∑ d, ∑ a, ∑ b, H a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, H a b c d = ∑ a, ∑ c, ∑ b, ∑ d, H a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, H a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, H a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, H a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma antisym_sum (H : Fin 4 → Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℂ))
    (hH : ∀ a b c d, H c b a d = -H a b c d) :
    ∑ a, ∑ b, ∑ c, ∑ d, H a b c d = 0 := by
  have hS : ∑ a, ∑ b, ∑ c, ∑ d, H a b c d = -∑ a, ∑ b, ∑ c, ∑ d, H a b c d := by
    calc ∑ a, ∑ b, ∑ c, ∑ d, H a b c d = ∑ c, ∑ b, ∑ a, ∑ d, H a b c d :=
          reorder3 (fun a b c => ∑ d, H a b c d)
      _ = ∑ c, ∑ b, ∑ a, ∑ d, -H c b a d :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => hH c b a d
      _ = -∑ a, ∑ b, ∑ c, ∑ d, H a b c d := by simp only [Finset.sum_neg_distrib]
  have h2 : (2:ℂ) • ∑ a, ∑ b, ∑ c, ∑ d, H a b c d = 0 := by
    rw [two_smul]; nth_rewrite 2 [hS]; exact add_neg_cancel _
  rcases smul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

end RS69

open DiracEquation RaritaSchwinger in
theorem solution (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g)
    (m : ℝ) (hm : 0 < m) (psi : VectorSpinorField) (hpsi : ContDiff ℝ 2 psi)
    (hEq : IsMassiveRSSolution g m psi) :
    ∀ x, gammaTrace g psi x = 0 ∧ divergence psi x = 0 := by
  have hf : ∀ nu, ContDiff ℝ 2 (comp psi nu) := fun nu => contDiff_pi.mp hpsi nu
  have hd0 : ∀ nu x, DifferentiableAt ℝ (comp psi nu) x :=
    fun nu x => ((hf nu).differentiable (by norm_num)) x
  have hd1 : ∀ nu rho x, DifferentiableAt ℝ (fun y => pd (comp psi nu) rho y) x :=
    fun nu rho x => RS69.diff_pd (hf nu) rho x
  -- Step 1: the divergence of the field equation
  have hA : ∀ x, ∑ mu, ∑ nu, sigma g mu nu *ᵥ pd (comp psi nu) mu x = 0 := by
    intro x
    have h1 : ∀ mu, (∑ kappa, ∑ rho, ∑ nu, levi mu kappa rho nu • (gamma5 g * gammaLower g kappa) *ᵥ
        pd (fun y => pd (comp psi nu) rho y) mu x)
        - (Complex.I * (m : ℂ)) • ∑ nu, sigma g mu nu *ᵥ pd (comp psi nu) mu x = 0 := by
      intro mu
      rw [← RS69.pd_eq (levi mu) (fun kappa => gamma5 g * gammaLower g kappa) (Complex.I * (m : ℂ))
        (sigma g mu) (comp psi) x (fun nu => hd0 nu x) (fun nu rho => hd1 nu rho x) mu]
      have hz : (fun y => (∑ kappa, ∑ rho, ∑ nu, levi mu kappa rho nu •
          (gamma5 g * gammaLower g kappa) *ᵥ pd (comp psi nu) rho y)
          - (Complex.I * (m : ℂ)) • ∑ nu, sigma g mu nu *ᵥ comp psi nu y) = fun _ => 0 :=
        funext fun y => hEq y mu
      rw [hz, RS69.pd_zero]
    have h2 : ∑ mu, ∑ kappa, ∑ rho, ∑ nu, levi mu kappa rho nu • (gamma5 g * gammaLower g kappa) *ᵥ
        pd (fun y => pd (comp psi nu) rho y) mu x = 0 := by
      apply RS69.antisym_sum
      intro a b c d
      rw [RS69.levi_swap02, RS69.pd2_symm (hf d) a c x, neg_smul]
    have h3 := Finset.sum_eq_zero (s := Finset.univ) (fun mu _ => h1 mu)
    rw [Finset.sum_sub_distrib, h2, ← Finset.smul_sum, zero_sub, neg_eq_zero, smul_eq_zero] at h3
    rcases h3 with h | h
    · exfalso
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      exact (mul_ne_zero Complex.I_ne_zero this) h
    · exact h
  -- Step 2: contract with the lowered gamma matrices
  have hT : ∀ x, gammaTrace g psi x = 0 := by
    intro x
    have h1 : ∑ mu, gammaLower g mu *ᵥ ((∑ kappa, ∑ rho, ∑ nu, levi mu kappa rho nu •
        (gamma5 g * gammaLower g kappa) *ᵥ pd (comp psi nu) rho x)
        - (Complex.I * (m : ℂ)) • ∑ nu, sigma g mu nu *ᵥ psi x nu) = 0 := by
      simp only [hEq x, mulVec_zero, Finset.sum_const_zero]
    have P1 : ∑ mu, gammaLower g mu *ᵥ (∑ kappa, ∑ rho, ∑ nu, levi mu kappa rho nu •
        (gamma5 g * gammaLower g kappa) *ᵥ pd (comp psi nu) rho x) = 0 := by
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      rw [RS69.reorder4 (fun mu kappa rho nu => levi mu kappa rho nu •
        (gammaLower g mu * (gamma5 g * gammaLower g kappa)) *ᵥ pd (comp psi nu) rho x)]
      have : ∀ rho nu, ∑ mu, ∑ kappa, levi mu kappa rho nu •
          (gammaLower g mu * (gamma5 g * gammaLower g kappa)) *ᵥ pd (comp psi nu) rho x
          = (-2 : ℂ) • sigma g rho nu *ᵥ pd (comp psi nu) rho x := by
        intro rho nu
        rw [← smul_mulVec, ← RS69.I1 hg rho nu, Matrix.sum_mulVec]
        refine Finset.sum_congr rfl fun mu _ => ?_
        rw [Matrix.sum_mulVec]
        refine Finset.sum_congr rfl fun kappa _ => ?_
        rw [smul_mulVec]
      simp only [this, ← Finset.smul_sum, hA x, smul_zero]
    have P2 : ∑ mu, gammaLower g mu *ᵥ (∑ nu, sigma g mu nu *ᵥ psi x nu)
        = (3 * Complex.I) • gammaTrace g psi x := by
      simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec]
      rw [Finset.sum_comm, gammaTrace, Finset.smul_sum]
      refine Finset.sum_congr rfl fun nu _ => ?_
      rw [← Matrix.sum_mulVec, RS69.I2 hg nu, smul_mulVec]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
      P1, P2, zero_sub, neg_eq_zero, smul_smul] at h1
    rcases smul_eq_zero.mp h1 with h | h
    · exfalso
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      have h3 : (3 : ℂ) ≠ 0 := by norm_num
      exact (mul_ne_zero (mul_ne_zero Complex.I_ne_zero this) (mul_ne_zero h3 Complex.I_ne_zero)) h
    · exact h
  -- Step 3: the divergence
  intro x
  refine ⟨hT x, ?_⟩
  have hTd : ∀ mu, ∑ nu, g nu *ᵥ pd (comp psi nu) mu x = 0 := by
    intro mu
    have e1 : pd (fun y => ∑ nu, g nu *ᵥ comp psi nu y) mu x
        = ∑ nu, g nu *ᵥ pd (comp psi nu) mu x := by
      rw [RS69.pd_sum Finset.univ (fun nu y => g nu *ᵥ comp psi nu y) (fun nu => RS69.diff_mulVec _ (hd0 nu x))]
      exact Finset.sum_congr rfl fun nu _ => RS69.pd_mulVec _ (hd0 nu x) mu
    rw [← e1]
    have hz : (fun y => ∑ nu, g nu *ᵥ comp psi nu y) = fun _ => 0 := funext fun y => hT y
    rw [hz, RS69.pd_zero]
  have hdiag : ∀ mu, ∑ nu, (Complex.I * eta mu nu) • pd (comp psi nu) mu x
      = Complex.I • (eta mu mu • pd (comp psi mu) mu x) := by
    intro mu
    rw [Finset.sum_eq_single mu, mul_smul]
    · intro b _ hb
      simp [eta, Ne.symm hb]
    · simp
  have h := hA x
  simp only [RS69.sigma_eq hg, Matrix.sub_mulVec, smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    Finset.sum_sub_distrib, ← Finset.smul_sum, ← Matrix.mulVec_sum, hTd, Matrix.mulVec_zero,
    smul_zero, Finset.sum_const_zero, zero_sub, neg_eq_zero, hdiag] at h
  simp only [Finset.sum_neg_distrib, neg_eq_zero, ← Finset.smul_sum] at h
  rcases smul_eq_zero.mp h with h' | h'
  · exact absurd h' Complex.I_ne_zero
  · exact h'
