-- Prove2me | solution 1 for SYKFastMix.FastMixing.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:39:39.592511+00:00
-- url     : https://prove2.me/submissions/f08dc586-9d31-4384-b476-dc344c8400a3

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

section
namespace SYKFastMix.FastMixing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def act (T : Super ι) : Mat ι →L[ℂ] Mat ι where
  toFun := applySuper T
  map_add' X Y := by ext a b; simp [applySuper, mul_add, Finset.sum_add_distrib]
  map_smul' z X := by ext a b; simp [applySuper, Finset.mul_sum, mul_left_comm]
  cont := by unfold applySuper; fun_prop

@[simp] lemma act_apply (T : Super ι) (X : Mat ι) : act T X = applySuper T X := rfl

lemma applySuper_mul (T U : Super ι) (X : Mat ι) :
    applySuper (T * U) X = applySuper T (applySuper U X) := by
  ext a b
  simp only [applySuper, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

def actAlgHom : Super ι →ₐ[ℂ] (Mat ι →L[ℂ] Mat ι) where
  toFun := act
  map_one' := by ext X a b; simp [act, applySuper, Matrix.one_apply]
  map_mul' T U := by ext1 X; exact applySuper_mul T U X
  map_zero' := by ext X a b; simp [act, applySuper]
  map_add' T U := by ext X a b; simp [act, applySuper, add_mul, Finset.sum_add_distrib]
  commutes' z := by
    ext X a b
    simp [act, applySuper, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

lemma act_exp (T : Super ι) : act (mexp T) = NormedSpace.exp (act T) := by
  letI : NormedAlgebra ℚ (Super ι) := .restrictScalars ℚ ℂ (Super ι)
  exact NormedSpace.map_exp (actAlgHom (ι := ι))
    (actAlgHom (ι := ι)).toLinearMap.continuous_of_finiteDimensional T

lemma applySuper_super (f : Mat ι →ₗ[ℂ] Mat ι) (X : Mat ι) :
    applySuper (super f) X = f X := by
  ext a b
  change (∑ p : ι × ι, f (Matrix.single p.1 p.2 1) a b * X p.1 p.2) = f X a b
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℂ) by simp]
  rw [map_smul]
  change _ = X i j * f (Matrix.single i j 1) a b
  exact mul_comm _ _

def evalSuper (X : Mat ι) : Super ι →L[ℂ] Mat ι where
  toFun := fun T ↦ applySuper T X
  map_add' T U := by ext a b; simp [applySuper, add_mul, Finset.sum_add_distrib]
  map_smul' z T := by ext a b; simp [applySuper, Finset.mul_sum, mul_assoc]
  cont := by unfold applySuper; fun_prop

@[simp] lemma evalSuper_apply (X : Mat ι) (T : Super ι) : evalSuper X T = applySuper T X := rfl

lemma applySuper_smul (z : ℂ) (T : Super ι) (X : Mat ι) :
    applySuper (z • T) X = z • applySuper T X := (evalSuper X).map_smul z T

def leftAct (H : Mat ι) : Mat ι →L[ℂ] Mat ι := ContinuousLinearMap.mul ℂ (Mat ι) H
def rightAct (H : Mat ι) : Mat ι →L[ℂ] Mat ι := (ContinuousLinearMap.mul ℂ (Mat ι)).flip H

@[simp] lemma leftAct_apply (H X : Mat ι) : leftAct H X = H * X := rfl
@[simp] lemma rightAct_apply (H X : Mat ι) : rightAct H X = X * H := rfl

lemma act_ad (H : Mat ι) : act (ad H) = leftAct H - rightAct H := by
  ext1 X
  exact applySuper_super (leftAct H - rightAct H).toLinearMap X

lemma act_smul (s : ℂ) (T : Super ι) : act (s • T) = s • act T :=
  (actAlgHom (ι := ι)).toLinearMap.map_smul s T

lemma leftAct_smul (s : ℂ) (H : Mat ι) : leftAct (s • H) = s • leftAct H := by
  ext1 X
  simp only [leftAct_apply, _root_.smul_apply, smul_mul_assoc]

lemma rightAct_smul (s : ℂ) (H : Mat ι) : rightAct (s • H) = s • rightAct H := by
  ext1 X
  simp only [rightAct_apply, _root_.smul_apply, mul_smul_comm]

lemma leftAct_pow_apply (H X : Mat ι) (n : ℕ) : (leftAct H ^ n) X = H^n * X := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ']; simp [ih, mul_assoc]

lemma rightAct_pow_apply (H X : Mat ι) (n : ℕ) : (rightAct H ^ n) X = X * H^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ]; simp [ih, mul_assoc]

lemma exp_leftAct_apply (H X : Mat ι) : NormedSpace.exp (leftAct H) X = mexp H * X := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (leftAct H)).mapL
    (ContinuousLinearMap.apply ℂ (Mat ι) X)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) H).mapL (rightAct X)
  apply HasSum.unique h1
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
    leftAct_pow_apply, rightAct_apply, smul_mul_assoc, mexp] using h2

lemma exp_rightAct_apply (H X : Mat ι) : NormedSpace.exp (rightAct H) X = X * mexp H := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (rightAct H)).mapL
    (ContinuousLinearMap.apply ℂ (Mat ι) X)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) H).mapL (leftAct X)
  apply HasSum.unique h1
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
    rightAct_pow_apply, leftAct_apply, mul_smul_comm, mexp] using h2

lemma exp_ad_apply (H X : Mat ι) (s : ℂ) :
    applySuper (mexp (s • ad H)) X = mexp (s • H) * X * mexp ((-s) • H) := by
  letI : NormedAlgebra ℚ (Mat ι →L[ℂ] Mat ι) :=
    .restrictScalars ℚ ℂ (Mat ι →L[ℂ] Mat ι)
  have he : act (s • ad H) = leftAct (s • H) + rightAct ((-s) • H) := by
    rw [act_smul, act_ad, leftAct_smul, rightAct_smul]
    module
  have hcomm : Commute (leftAct (s • H)) (rightAct ((-s) • H)) := by
    apply ContinuousLinearMap.ext
    intro X
    change (s • H) * (X * ((-s) • H)) = ((s • H) * X) * ((-s) • H)
    exact (mul_assoc _ _ _).symm
  rw [← act_apply, act_exp, he]
  have hexp := NormedSpace.exp_add_of_commute (𝔸 := Mat ι →L[ℂ] Mat ι) hcomm
  have happ := congrArg (fun f : Mat ι →L[ℂ] Mat ι ↦ f X) hexp
  calc
    (NormedSpace.exp (leftAct (s • H) + rightAct ((-s) • H))) X =
        (NormedSpace.exp (leftAct (s • H)) * NormedSpace.exp (rightAct ((-s) • H))) X := happ
    _ = _ := by
      change NormedSpace.exp (leftAct (s • H)) (NormedSpace.exp (rightAct ((-s) • H)) X) = _
      rw [exp_leftAct_apply, exp_rightAct_apply]
      exact (mul_assoc _ _ _).symm


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def opVec (X : Mat ι) : ι × ι → ℂ := fun p => X p.1 p.2

lemma opVec_eq_zero_iff (X : Mat ι) : opVec X = 0 ↔ X = 0 := by
  constructor
  · intro h
    ext a b
    have hab := congrFun h (a, b)
    exact hab
  · rintro rfl
    rfl

lemma hsInner_eq_dotProduct (X Y : Mat ι) :
    hsInner X Y = star (opVec X) ⬝ᵥ opVec Y := by
  simp only [hsInner, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diag, dotProduct, opVec, Fintype.sum_prod_type]
  change (∑ i, ∑ j, star (X j i) * Y j i) =
    ∑ i, ∑ j, star (X i j) * Y i j
  rw [Finset.sum_comm]

lemma opVec_applySuper (T : Super ι) (X : Mat ι) :
    opVec (applySuper T X) = T *ᵥ opVec X := rfl

lemma hsInner_adj_mul (T : Super ι) (X : Mat ι) :
    hsInner X (applySuper (Tᴴ * T) X) = hsInner (applySuper T X) (applySuper T X) := by
  rw [hsInner_eq_dotProduct, hsInner_eq_dotProduct]
  rw [opVec_applySuper, opVec_applySuper]
  change star (opVec X) ⬝ᵥ ((Tᴴ * T) *ᵥ opVec X) =
    star (T *ᵥ opVec X) ⬝ᵥ (T *ᵥ opVec X)
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  rw [star_star]

lemma qform_adj_mul (T : Super ι) (X : Mat ι) :
    qform (Tᴴ * T) X = hsSq (applySuper T X) := by
  exact congrArg Complex.re (hsInner_adj_mul T X)

lemma qform_sum_adj_mul {I : Type} [Fintype I] (T : I → Super ι) (X : Mat ι) :
    qform (∑ i, (T i)ᴴ * T i) X = ∑ i, hsSq (applySuper (T i) X) := by
  rw [qform, hsInner_eq_dotProduct, opVec_applySuper]
  rw [show (∑ i, (T i)ᴴ * T i) *ᵥ opVec X =
      ∑ i, ((T i)ᴴ * T i) *ᵥ opVec X by
    simpa using Matrix.sum_mulVec Finset.univ (fun i ↦ (T i)ᴴ * T i) (opVec X)]
  rw [dotProduct_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsSq, ← hsInner_adj_mul]
  rw [hsInner_eq_dotProduct, opVec_applySuper]

lemma hsSq_eq_sum_norm_sq (X : Mat ι) :
    hsSq X = ∑ p : ι × ι, ‖opVec X p‖ ^ 2 := by
  rw [hsSq, hsInner_eq_dotProduct]
  simp only [dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Complex.sq_norm]
  change (conj (opVec X p) * opVec X p).re = Complex.normSq (opVec X p)
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

lemma hsSq_nonneg (X : Mat ι) : 0 ≤ hsSq X := by
  rw [hsSq_eq_sum_norm_sq]
  positivity

lemma hsSq_eq_zero_iff (X : Mat ι) : hsSq X = 0 ↔ X = 0 := by
  rw [hsSq_eq_sum_norm_sq]
  constructor
  · intro h
    have hzfun : (fun p : ι × ι ↦ ‖opVec X p‖ ^ 2) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _)).mp h
    have hz : ∀ p : ι × ι, ‖opVec X p‖ ^ 2 = 0 := fun p ↦ congrFun hzfun p
    ext a b
    have hab := hz (a, b)
    simp only [sq_eq_zero_iff, norm_eq_zero] at hab
    exact hab
  · rintro rfl
    simp [opVec]

lemma applySuper_sum_adj_mul_eq_zero_iff {I : Type} [Fintype I]
    (T : I → Super ι) (X : Mat ι) :
    applySuper (∑ i, (T i)ᴴ * T i) X = 0 ↔ ∀ i, applySuper (T i) X = 0 := by
  constructor
  · intro h i
    have hq : qform (∑ i, (T i)ᴴ * T i) X = 0 := by
      simp [qform, h, hsInner, applySuper]
    rw [qform_sum_adj_mul] at hq
    have hifun : (fun j ↦ hsSq (applySuper (T j) X)) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg (fun j ↦ hsSq_nonneg _)).mp hq
    have hi : hsSq (applySuper (T i) X) = 0 := congrFun hifun i
    exact (hsSq_eq_zero_iff _).mp hi
  · intro h
    apply (opVec_eq_zero_iff _).mp
    rw [opVec_applySuper]
    rw [show (∑ i, (T i)ᴴ * T i) *ᵥ opVec X =
        ∑ i, ((T i)ᴴ * T i) *ᵥ opVec X by
      simpa using Matrix.sum_mulVec Finset.univ (fun i ↦ (T i)ᴴ * T i) (opVec X)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Matrix.mulVec_mulVec, ← opVec_applySuper, h i]
    change (T i)ᴴ *ᵥ (0 : ι × ι → ℂ) = 0
    exact Matrix.mulVec_zero _


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]
lemma hsInner_sub_left (X Y Z : Mat ι) : hsInner (X-Y) Z = hsInner X Z - hsInner Y Z := by
  simp [hsInner, Matrix.conjTranspose_sub, sub_mul]

lemma hsInner_sub_right (X Y Z : Mat ι) : hsInner X (Y-Z) = hsInner X Y - hsInner X Z := by
  simp [hsInner, mul_sub]

lemma hsInner_smul_left (z : ℂ) (X Y : Mat ι) : hsInner (z • X) Y = conj z * hsInner X Y := by
  simp [hsInner, Matrix.conjTranspose_smul, smul_mul_assoc]

lemma hsInner_smul_right (z : ℂ) (X Y : Mat ι) : hsInner X (z • Y) = z * hsInner X Y := by
  simp [hsInner, mul_smul_comm]

lemma hsInner_conj_symm (X Y : Mat ι) : hsInner X Y = conj (hsInner Y X) := by
  unfold hsInner
  change (Xᴴ * Y).trace = star ((Yᴴ * X).trace)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

lemma hsInner_self_real (X : Mat ι) : hsInner X X = (hsSq X : ℂ) := by
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im (hsInner_conj_symm X X)
    simp only [Complex.conj_im] at h
    simp only [Complex.ofReal_im]
    linarith


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : NormedAlgebra ℚ (Mat ι) := .restrictScalars ℚ ℂ (Mat ι)

lemma mexp_smul_add (H : Mat ι) (a b : ℂ) :
    mexp (a • H) * mexp (b • H) = mexp ((a+b) • H) := by
  have hc : Commute (a • H) (b • H) := by
    change (a • H) * (b • H) = (b • H) * (a • H)
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm a b]
  exact (NormedSpace.exp_add_of_commute (𝔸 := Mat ι) hc).symm.trans (by rw [← add_smul]; rfl)

lemma mexp_smul_cancel (H : Mat ι) (a : ℂ) : mexp (a • H) * mexp ((-a) • H) = 1 := by
  rw [mexp_smul_add]
  simp [mexp]

lemma mexp_hermitian (H : Mat ι) (hH : H.IsHermitian) (a : ℝ) :
    (mexp ((a : ℂ) • H)).IsHermitian := by
  exact (hH.smul (by simp [IsSelfAdjoint])).exp

lemma mexp_spectral (H : Mat ι) (hH : H.IsHermitian) (a : ℝ) :
    mexp ((a : ℂ) • H) = Unitary.conjStarAlgAut ℂ (Mat ι) hH.eigenvectorUnitary
      (Matrix.diagonal (fun i ↦ (Real.exp (a * hH.eigenvalues i) : ℂ))) := by
  let U := Unitary.conjStarAlgAut ℂ (Mat ι) hH.eigenvectorUnitary
  letI : NormedAlgebra ℚ (Mat ι) := .restrictScalars ℚ ℂ (Mat ι)
  have hm := NormedSpace.map_exp U U.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
    (Matrix.diagonal (fun i ↦ (a * hH.eigenvalues i : ℂ)))
  have hdiag : (a : ℂ) • H = U (Matrix.diagonal (fun i ↦ (a * hH.eigenvalues i : ℂ))) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [← map_smul, ← Matrix.diagonal_smul]
    rfl
  change NormedSpace.exp ((a : ℂ) • H) = _
  rw [hdiag, ← hm, Matrix.exp_diagonal]
  congr 1
  congr 1
  funext i
  simp only [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_mul,
    Complex.ofReal_exp]

lemma mexp_trace (H : Mat ι) (hH : H.IsHermitian) (a : ℝ) :
    Matrix.trace (mexp ((a : ℂ) • H)) = (∑ i, Real.exp (a * hH.eigenvalues i) : ℝ) := by
  rw [mexp_spectral H hH a, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp

lemma mexp_trace_pos [Nonempty ι] (H : Mat ι) (hH : H.IsHermitian) (a : ℝ) :
    0 < (Matrix.trace (mexp ((a : ℂ) • H))).re := by
  rw [mexp_trace H hH a, Complex.ofReal_re]
  exact Finset.sum_pos (fun i hi ↦ Real.exp_pos _) Finset.univ_nonempty

lemma mexp_half_hsSq (H : Mat ι) (hH : H.IsHermitian) (β : ℝ) :
    hsSq (mexp (((-(β/2) : ℝ) : ℂ) • H)) =
      (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re := by
  rw [hsSq, hsInner, (mexp_hermitian H hH (-(β/2))).eq, mexp_smul_add]
  congr 3
  push_cast
  ring


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma applySuper_one (X : Mat ι) : applySuper (1 : Super ι) X = X := by
  ext i j
  simp [applySuper, Matrix.one_apply]

lemma applySuper_neg (T : Super ι) (X : Mat ι) : applySuper (-T) X = -applySuper T X := by
  ext i j
  simp [applySuper, Finset.sum_neg_distrib]

lemma applySuper_ext {T U : Super ι} (h : ∀ X, applySuper T X = applySuper U X) : T = U := by
  ext a b
  have hab := congrArg (fun X : Mat ι ↦ X a.1 a.2) (h (Matrix.single b.1 b.2 1))
  simpa [applySuper, Matrix.single_apply, ite_and, apply_ite,
    Fintype.sum_prod_type, eq_comm] using hab

def sandwichSuper (C : Mat ι) : Super ι := super (fun X ↦ C*X*C)

lemma applySuper_sandwich (C X : Mat ι) : applySuper (sandwichSuper C) X = C*X*C :=
  applySuper_super ((rightAct C).comp (leftAct C)).toLinearMap X

lemma sandwichSuper_mul {C B : Mat ι} (hCB : C*B=1) (hBC : B*C=1) :
    sandwichSuper C * sandwichSuper B = 1 := by
  apply applySuper_ext
  intro X
  rw [applySuper_mul, applySuper_sandwich, applySuper_sandwich, applySuper_one]
  calc
    C*(B*X*B)*C = (C*B)*X*(B*C) := by noncomm_ring
    _ = X := by rw [hCB, hBC, one_mul, mul_one]

lemma mexp_similarity (S Sinv T : Super ι) (hS : S*Sinv=1) (hiS : Sinv*S=1) :
    mexp (S*T*Sinv) = S*mexp T*Sinv := by
  let u : (Super ι)ˣ := ⟨S, Sinv, hS, hiS⟩
  exact Matrix.exp_units_conj u T

lemma super_sandwich_action (B C : Mat ι) (T : Super ι) :
    super (fun X ↦ -(B * applySuper T (C*X*C) * B)) =
      -(sandwichSuper B * T * sandwichSuper C) := by
  apply applySuper_ext
  intro X
  rw [applySuper_neg, applySuper_mul, applySuper_mul, applySuper_sandwich, applySuper_sandwich]
  have he := applySuper_super
    (- ((rightAct B).comp ((leftAct B).comp ((act T).comp
      ((rightAct C).comp (leftAct C)))))).toLinearMap X
  exact he

lemma discriminant_similarity {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (β : ℝ) :
    discriminant H γ β = - (sandwichSuper (mexp (((β/4 : ℝ) : ℂ) • H)) *
      lindblad H γ β * sandwichSuper (mexp (((-(β/4) : ℝ) : ℂ) • H))) := by
  simpa only [discriminant, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat] using
    super_sandwich_action (mexp (((β/4 : ℝ) : ℂ) • H))
      (mexp (((-(β/4) : ℝ) : ℂ) • H)) (lindblad H γ β)

lemma evolve_discriminant_similarity {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι)
    (β t : ℝ) (X : Mat ι) :
    evolve (lindblad H γ β) t X =
      mexp (((-(β/4) : ℝ) : ℂ) • H) *
        applySuper (mexp (((-t : ℝ) : ℂ) • discriminant H γ β))
          (mexp (((β/4 : ℝ) : ℂ) • H) * X * mexp (((β/4 : ℝ) : ℂ) • H)) *
      mexp (((-(β/4) : ℝ) : ℂ) • H) := by
  let C := mexp (((-(β/4) : ℝ) : ℂ) • H)
  let B := mexp (((β/4 : ℝ) : ℂ) • H)
  let S := sandwichSuper C
  let Sinv := sandwichSuper B
  have hCB : C*B=1 := by
    change mexp (((-(β/4) : ℝ) : ℂ) • H) * mexp (((β/4 : ℝ) : ℂ) • H) = 1
    rw [mexp_smul_add]
    have he : (((-(β/4) : ℝ) : ℂ)) + (((β/4 : ℝ) : ℂ)) = 0 := by push_cast; ring
    rw [he]
    simp [mexp]
  have hBC : B*C=1 := by
    change mexp (((β/4 : ℝ) : ℂ) • H) * mexp (((-(β/4) : ℝ) : ℂ) • H) = 1
    rw [mexp_smul_add]
    have he : (((β/4 : ℝ) : ℂ)) + (((-(β/4) : ℝ) : ℂ)) = 0 := by push_cast; ring
    rw [he]
    simp [mexp]
  have hS : S*Sinv=1 := sandwichSuper_mul hCB hBC
  have hiS : Sinv*S=1 := sandwichSuper_mul hBC hCB
  have hD : discriminant H γ β = -(Sinv*lindblad H γ β*S) := discriminant_similarity H γ β
  have hL : (t : ℂ) • lindblad H γ β = S * (((-t : ℝ) : ℂ) • discriminant H γ β) * Sinv := by
    rw [hD]
    simp only [Complex.ofReal_neg, neg_smul, smul_neg, neg_neg,
      mul_smul_comm, smul_mul_assoc]
    have he : S*(Sinv*lindblad H γ β*S)*Sinv = lindblad H γ β := by
      calc
        _ = (S*Sinv)*lindblad H γ β*(S*Sinv) := by noncomm_ring
        _ = _ := by rw [hS, one_mul, mul_one]
    rw [he]
  unfold evolve
  rw [hL, mexp_similarity S Sinv _ hS hiS, applySuper_mul, applySuper_mul,
    applySuper_sandwich, applySuper_sandwich]


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def hsVec (X : Mat ι) : EuclideanSpace ℂ (ι × ι) := WithLp.toLp 2 (opVec X)
def hsUnvec (x : EuclideanSpace ℂ (ι × ι)) : Mat ι := fun i j ↦ x (i,j)

lemma hsVec_hsUnvec (x : EuclideanSpace ℂ (ι × ι)) : hsVec (hsUnvec x)=x := by
  apply PiLp.ext
  intro i
  rfl

lemma hsVec_injective : Function.Injective (hsVec : Mat ι → EuclideanSpace ℂ (ι × ι)) := by
  intro X Y h
  ext i j
  exact congrArg (fun x : EuclideanSpace ℂ (ι × ι) ↦ x (i,j)) h

lemma hsVec_norm (X : Mat ι) : ‖hsVec X‖ = hs X := by
  have h : ‖hsVec X‖^2=hsSq X := by
    rw [EuclideanSpace.norm_sq_eq, hsSq_eq_sum_norm_sq]
    rfl
  rw [hs, ← h, Real.sqrt_sq (norm_nonneg _)]

lemma hsVec_norm_sq (X : Mat ι) : ‖hsVec X‖^2=hsSq X := by
  rw [hsVec_norm, hs, Real.sq_sqrt (hsSq_nonneg _)]

lemma hsVec_smul (z : ℂ) (X : Mat ι) : hsVec (z • X)=z • hsVec X := by
  apply PiLp.ext
  intro i
  rfl

lemma hsVec_inner (X Y : Mat ι) : inner ℂ (hsVec X) (hsVec Y)=hsInner X Y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, hsInner_eq_dotProduct, dotProduct_comm]
  rfl

lemma hsVec_applySuper (T : Super ι) (X : Mat ι) :
    hsVec (applySuper T X) = (Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) T) (hsVec X) := by
  apply PiLp.ext
  intro i
  rfl


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma hsInner_add_right (X Y Z : Mat ι) : hsInner X (Y+Z)=hsInner X Y+hsInner X Z := by
  simp [hsInner, mul_add]

lemma hsInner_neg_right (X Y : Mat ι) : hsInner X (-Y)=-hsInner X Y := by
  simp [hsInner]

lemma hsInner_applySuper_adjoint (T : Super ι) (X Y : Mat ι) :
    hsInner (applySuper T X) Y=hsInner X (applySuper Tᴴ Y) := by
  rw [hsInner_eq_dotProduct, hsInner_eq_dotProduct, opVec_applySuper, opVec_applySuper,
    Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]

lemma hsInner_leftMul (A X Y : Mat ι) : hsInner (A*X) Y=hsInner X (Aᴴ*Y) := by
  simp only [hsInner, Matrix.conjTranspose_mul, mul_assoc]

lemma hsInner_rightMul (A X Y : Mat ι) : hsInner (X*A) Y=hsInner X (Y*Aᴴ) := by
  simp only [hsInner, Matrix.conjTranspose_mul]
  calc
    Matrix.trace (Aᴴ*Xᴴ*Y) = Matrix.trace (Aᴴ*(Xᴴ*Y)) := by rw [mul_assoc]
    _ = Matrix.trace ((Xᴴ*Y)*Aᴴ) := Matrix.trace_mul_comm _ _
    _ = _ := by rw [mul_assoc]


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

lemma applySuper_add {ι : Type} [Fintype ι] [DecidableEq ι] (T U : Super ι) (X : Mat ι) :
    applySuper (T+U) X=applySuper T X+applySuper U X := (evalSuper X).map_add T U

@[simp] lemma applySuper_zero {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) :
    applySuper (0 : Super ι) X=0 := (evalSuper X).map_zero


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

lemma rawString_hermitian_of_card_four {N : ℕ} (Q : Model N)
    (S : Finset (Fin N)) (hS : S.card = 4) : (rawString Q S).IsHermitian := by
  unfold rawString Matrix.IsHermitian
  rw [Matrix.conjTranspose_list_prod]
  have hlen : (S.sort (· ≤ ·)).length = 4 := by simpa using hS
  have hnodup : (S.sort (· ≤ ·)).Nodup := S.sort_nodup (· ≤ ·)
  obtain ⟨a, b, c, d, hlist⟩ := List.length_eq_four.mp hlen
  rw [hlist] at hnodup
  simp at hnodup
  rcases hnodup with ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
  rw [hlist]
  simp
  rw [(Q.car.herm a).eq, (Q.car.herm b).eq, (Q.car.herm c).eq, (Q.car.herm d).eq]
  calc
    Q.γ d * (Q.γ c * (Q.γ b * Q.γ a)) =
        (Q.γ d * Q.γ c) * (Q.γ b * Q.γ a) := by noncomm_ring
    _ = -(Q.γ c * Q.γ d) * (Q.γ b * Q.γ a) := by
          rw [Q.car.anticomm d c (Ne.symm hcd)]
    _ = Q.γ c * (-(Q.γ d * Q.γ b) * Q.γ a) := by noncomm_ring
    _ = Q.γ c * (Q.γ b * Q.γ d * Q.γ a) := by
          rw [Q.car.anticomm d b (Ne.symm hbd)]
          noncomm_ring
    _ = (Q.γ c * Q.γ b) * (Q.γ d * Q.γ a) := by noncomm_ring
    _ = -(Q.γ b * Q.γ c) * (Q.γ d * Q.γ a) := by
          rw [Q.car.anticomm c b (Ne.symm hbc)]
    _ = Q.γ b * Q.γ c * (Q.γ a * Q.γ d) := by
          rw [Q.car.anticomm d a (Ne.symm had)]
          noncomm_ring
    _ = Q.γ b * (Q.γ c * Q.γ a) * Q.γ d := by noncomm_ring
    _ = -(Q.γ b * (Q.γ a * Q.γ c) * Q.γ d) := by
          rw [Q.car.anticomm c a (Ne.symm hac)]
          noncomm_ring
    _ = -((Q.γ b * Q.γ a) * (Q.γ c * Q.γ d)) := by noncomm_ring
    _ = (Q.γ a * Q.γ b) * (Q.γ c * Q.γ d) := by
          rw [Q.car.anticomm b a (Ne.symm hab)]
          noncomm_ring
    _ = Q.γ a * (Q.γ b * (Q.γ c * Q.γ d)) := by noncomm_ring

lemma hamiltonian_hermitian_words {N : ℕ} (Q : Model N) (w : Disorder N) :
    (hamiltonian Q w).IsHermitian := by
  unfold hamiltonian Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Matrix.conjTranspose_smul, (rawString_hermitian_of_card_four Q A.1 A.2).eq]
  simp


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma sylvester_hs_identity (A U : Mat ι) (hU : U.IsHermitian) :
    (hsInner A (A*(U*U)+(U*U)*A)).re=hsSq (A*U)+hsSq (U*A) := by
  rw [hsInner_add_right]
  change (hsInner A (A*(U*U))).re+(hsInner A ((U*U)*A)).re=_
  have h1 : hsInner A (A*(U*U))=hsInner (A*U) (A*U) := by
    rw [hsInner_rightMul, hU.eq]
    simp only [mul_assoc]
  have h2 : hsInner A ((U*U)*A)=hsInner (U*A) (U*A) := by
    rw [hsInner_leftMul, hU.eq]
    simp only [mul_assoc]
  rw [h1,h2]
  rfl

lemma sylvester_zero (A U V : Mat ι) (hU : U.IsHermitian) (hUV : U*V=1)
    (hA : A*(U*U)+(U*U)*A=0) : A=0 := by
  have h := sylvester_hs_identity A U hU
  rw [hA] at h
  have hz : hsSq (A*U)=0 := by
    have h0 : (hsInner A 0).re=0 := by simp [hsInner]
    rw [h0] at h
    nlinarith [hsSq_nonneg (A*U), hsSq_nonneg (U*A)]
  have hAU := (hsSq_eq_zero_iff (A*U)).mp hz
  calc
    A=A*(U*V) := by rw [hUV,mul_one]
    _=(A*U)*V := by rw [mul_assoc]
    _=0 := by rw [hAU,zero_mul]

lemma sylvester_posSemidef (D U V : Mat ι) (hU : U.IsHermitian) (hUV : U*V=1)
    (hR : (D*(U*U)+(U*U)*D).PosSemidef) : D.PosSemidef := by
  have hM : (U*U).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul,hU.eq]
  have hD : D.IsHermitian := by
    have hz : (D-Dᴴ)*(U*U)+(U*U)*(D-Dᴴ)=0 := by
      have hh := hR.isHermitian.eq
      simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_mul,hU.eq] at hh
      calc
        _=(D*(U*U)+(U*U)*D)-((U*U)*Dᴴ+Dᴴ*(U*U)) := by noncomm_ring
        _=0 := sub_eq_zero.mpr hh.symm
    exact (sub_eq_zero.mp (sylvester_zero _ U V hU hUV hz)).symm
  apply hD.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  change 0 ≤ hD.eigenvalues i
  let v : EuclideanSpace ℂ ι := hD.eigenvectorBasis i
  have hv : (v : ι → ℂ)≠0 := by
    intro he
    have he' : v=0 := by apply PiLp.ext; intro j; exact congrFun he j
    have hh : ‖v‖=1 := hD.eigenvectorBasis.orthonormal.norm_eq_one i
    rw [he',norm_zero] at hh
    norm_num at hh
  have he : D*ᵥ (v : ι → ℂ)=(hD.eigenvalues i : ℂ) • (v : ι → ℂ) :=
    hD.mulVec_eigenvectorBasis i
  have hUn : 0 < (star (U*ᵥ (v : ι → ℂ)) ⬝ᵥ (U*ᵥ (v : ι → ℂ))).re := by
    have hVU : V*U=1 := mul_eq_one_comm.mp hUV
    have hu : U*ᵥ (v : ι → ℂ)≠0 := by
      intro hu
      apply hv
      have ht := congrArg (fun z ↦ V*ᵥ z) hu
      simpa only [Matrix.mulVec_mulVec,hVU,Matrix.one_mulVec,Matrix.mulVec_zero] using ht
    have ht : 0 < star (U*ᵥ (v : ι → ℂ)) ⬝ᵥ (U*ᵥ (v : ι → ℂ)) :=
      dotProduct_star_self_pos_iff.mpr hu
    exact (Complex.pos_iff.mp ht).1
  have hp := hR.dotProduct_mulVec_nonneg (v : ι → ℂ)
  have hr : (star (v : ι → ℂ) ⬝ᵥ ((D*(U*U)+(U*U)*D)*ᵥ (v : ι → ℂ))) =
      (2*(hD.eigenvalues i) : ℝ) * (star (U*ᵥ (v : ι → ℂ)) ⬝ᵥ (U*ᵥ (v : ι → ℂ))) := by
    let LD := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) D
    let LU := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) U
    have hDs (x y : EuclideanSpace ℂ ι) : inner ℂ (LD x) y=inner ℂ x (LD y) :=
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hD) x y
    have hUs (x y : EuclideanSpace ℂ ι) : inner ℂ (LU x) y=inner ℂ x (LU y) :=
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hU) x y
    have hev : LD v=(hD.eigenvalues i : ℂ) • v := by
      apply PiLp.ext
      intro j
      exact congrFun he j
    have hinner : inner ℂ v (LD (LU (LU v))+LU (LU (LD v))) =
        (2*hD.eigenvalues i : ℝ) * inner ℂ (LU v) (LU v) := by
      rw [inner_add_right, ← hDs, hev, map_smul, map_smul,
        inner_smul_left,inner_smul_right, ← hUs v (LU v)]
      simp only [Complex.conj_ofReal]
      push_cast
      ring
    change (((D*ᵥ (U*ᵥ (U*ᵥ (v : ι → ℂ))))+(U*ᵥ (U*ᵥ (D*ᵥ (v : ι → ℂ))))) ⬝ᵥ
        star (v : ι → ℂ)) =
      (2*hD.eigenvalues i : ℝ) * ((U*ᵥ (v : ι → ℂ)) ⬝ᵥ star (U*ᵥ (v : ι → ℂ))) at hinner
    rw [Matrix.mulVec_mulVec _ U U, Matrix.mulVec_mulVec _ D (U*U),
      Matrix.mulVec_mulVec _ U D, Matrix.mulVec_mulVec _ U (U*D)] at hinner
    simpa only [← Matrix.mul_assoc, Matrix.add_mulVec, dotProduct_comm] using hinner
  have hp' : 0 ≤ (star (v : ι → ℂ) ⬝ᵥ ((D*(U*U)+(U*U)*D)*ᵥ (v : ι → ℂ))).re :=
    Complex.nonneg_iff.mp hp |>.1
  rw [hr] at hp'
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hp'
  nlinarith


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def rootProjection (r : Mat ι) : Super ι :=
  Matrix.of (fun p q ↦ r p.1 p.2 * conj (r q.1 q.2))

lemma rootProjection_hermitian (r : Mat ι) : (rootProjection r).IsHermitian := by
  ext p q
  simp [rootProjection,Matrix.conjTranspose_apply,mul_comm]

lemma applySuper_rootProjection (r X : Mat ι) :
    applySuper (rootProjection r) X=hsInner r X • r := by
  rw [hsInner_eq_dotProduct]
  ext i j
  simp only [applySuper,rootProjection,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,
    dotProduct,opVec,Pi.star_apply,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [← Complex.star_def]
  ring

lemma hsSq_orthogonal_projection (r X : Mat ι) (hr : hsSq r=1) :
    hsSq (X-hsInner r X • r)=hsSq X-‖hsInner r X‖^2 := by
  have hrr : hsInner r r=1 := by rw [hsInner_self_real,hr]; rfl
  have hXr : hsInner X r=conj (hsInner r X) := hsInner_conj_symm _ _
  unfold hsSq
  simp only [hsInner_sub_left,hsInner_sub_right,hsInner_smul_left,hsInner_smul_right,hrr,hXr]
  simp only [mul_one,sub_self,mul_zero,sub_zero]
  rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  simp
  norm_cast

lemma posSemidef_of_qform_nonneg (T : Super ι) (hT : T.IsHermitian)
    (hp : ∀ X : Mat ι, 0 ≤ qform T X) : T.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hT
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_,(hT.im_star_dotProduct_mulVec_self v).symm⟩
  have hh := hp (fun i j ↦ v (i,j))
  simp only [qform,hsInner_eq_dotProduct,opVec_applySuper] at hh
  change 0 ≤ (star v ⬝ᵥ (T*ᵥ v)).re at hh
  exact hh

lemma qform_nonneg_of_posSemidef (T : Super ι) (hp : T.PosSemidef) (X : Mat ι) :
    0 ≤ qform T X := by
  rw [qform,hsInner_eq_dotProduct,opVec_applySuper]
  exact hp.re_dotProduct_nonneg (opVec X)

lemma applySuper_sub (T U : Super ι) (X : Mat ι) :
    applySuper (T-U) X=applySuper T X-applySuper U X := (evalSuper X).map_sub T U

lemma gap_shift_posSemidef (K : Super ι) (r : Mat ι) (a : ℝ)
    (hr : hsSq r=1) (hg : HasGap K r a) :
    (K-(a : ℂ) • (1-rootProjection r)).PosSemidef := by
  have hP := rootProjection_hermitian r
  have hK : K.IsHermitian := hg.1
  have hherm : (K-(a : ℂ) • (1-rootProjection r)).IsHermitian := by
    unfold Matrix.IsHermitian
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
      hK.eq,hP.eq,Complex.star_def,Complex.conj_ofReal]
  apply posSemidef_of_qform_nonneg _ hherm
  intro X
  let z := hsInner r X
  let Y := X-z • r
  have ho : hsInner r Y=0 := by
    change hsInner r (X-z • r)=0
    rw [hsInner_sub_right,hsInner_smul_right,hsInner_self_real,hr]
    simp [z]
  have hKY : applySuper K Y=applySuper K X := by
    change (act K) (X-z • r)=_
    rw [map_sub,map_smul]
    change applySuper K X-z • applySuper K r=_
    rw [hg.2.2.1,smul_zero,sub_zero]
  have hq : qform K Y=qform K X := by
    have hh := hsInner_applySuper_adjoint K r X
    rw [hK.eq,hg.2.2.1] at hh
    have hroot : hsInner r (applySuper K X)=0 := by rw [← hh]; simp [hsInner]
    unfold qform
    rw [hKY]
    change (hsInner (X-z • r) (applySuper K X)).re=_
    rw [hsInner_sub_left,hsInner_smul_left,hroot,mul_zero,sub_zero]
  have hy := hg.2.2.2 Y ho
  rw [hq] at hy
  have hn : hsSq Y=hsSq X-‖z‖^2 := hsSq_orthogonal_projection r X hr
  rw [hn] at hy
  have hshift : qform (K-(a : ℂ) • (1-rootProjection r)) X =
      qform K X-a*(hsSq X-‖z‖^2) := by
    rw [qform,applySuper_sub,applySuper_smul,applySuper_sub,applySuper_one,applySuper_rootProjection,
      hsInner_sub_right,hsInner_smul_right,hsInner_sub_right,hsInner_smul_right]
    have hXr : hsInner X r=conj z := hsInner_conj_symm _ _
    rw [hXr]
    have he : z*conj z=(‖z‖^2 : ℝ) := by
      rw [mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    change (hsInner X (applySuper K X)-(a : ℂ)*(hsInner X X-z*conj z)).re=_
    rw [he,hsInner_self_real]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,Complex.ofReal_pow]
    norm_cast
  rw [hshift]
  linarith

lemma sylvester_gap (K D U V : Super ι) (r : Mat ι) (a : ℝ)
    (hr : hsSq r=1) (hg : HasGap K r a) (hU : U.IsHermitian) (hUV : U*V=1)
    (hUr : applySuper U r=r)
    (hSyl : D*(U*U)+(U*U)*D=(4 : ℂ) • (U*K*U)) : HasGap D r (2*a) := by
  have hK : K.PosSemidef := posSemidef_of_qform_nonneg K hg.1 hg.2.1
  have hR : (D*(U*U)+(U*U)*D).PosSemidef := by
    rw [hSyl]
    have hp := hK.mul_mul_conjTranspose_same U
    rw [hU.eq] at hp
    exact hp.smul (by norm_num : (0 : ℂ) ≤ 4)
  have hD := sylvester_posSemidef D U V hU hUV hR
  have hDr : applySuper D r=0 := by
    have he := congrArg (fun T : Super ι ↦ applySuper T r) hSyl
    simp only [applySuper_add,applySuper_mul,applySuper_smul,hUr,hg.2.2.1] at he
    have he0 : applySuper D r+applySuper U (applySuper U (applySuper D r))=0 := by
      have hzU : applySuper U (0 : Mat ι)=0 := (act U).map_zero
      simpa only [hzU,smul_zero] using he
    have hh := congrArg (fun Y ↦ (hsInner (applySuper D r) Y).re) he0
    rw [hsInner_add_right] at hh
    have hUinner : hsInner (applySuper D r) (applySuper U (applySuper U (applySuper D r)))=
        hsInner (applySuper U (applySuper D r)) (applySuper U (applySuper D r)) := by
      simpa only [hU.eq] using
        (hsInner_applySuper_adjoint U (applySuper D r) (applySuper U (applySuper D r))).symm
    rw [hUinner] at hh
    have hz : hsSq (applySuper D r)=0 := by
      change hsSq (applySuper D r)+hsSq (applySuper U (applySuper D r))=(hsInner (applySuper D r) 0).re at hh
      have hzero : (hsInner (applySuper D r) 0).re=0 := by simp [hsInner]
      rw [hzero] at hh
      nlinarith [hsSq_nonneg (applySuper D r),hsSq_nonneg (applySuper U (applySuper D r))]
    exact (hsSq_eq_zero_iff _).mp hz
  have hUP : U*rootProjection r=rootProjection r := by
    apply applySuper_ext
    intro X
    rw [applySuper_mul,applySuper_rootProjection]
    change (act U) (hsInner r X • r)=_
    rw [map_smul]
    change hsInner r X • applySuper U r=_
    rw [hUr]
  have hPU : rootProjection r*U=rootProjection r := by
    have he := congrArg Matrix.conjTranspose hUP
    simpa only [Matrix.conjTranspose_mul,(rootProjection_hermitian r).eq,hU.eq] using he
  let C := 1-rootProjection r
  have hUC : U*C*U=U*U-rootProjection r := by
    dsimp only [C]
    rw [mul_sub,mul_one,sub_mul,hUP,hPU]
  have hCM : C*(U*U)+(U*U)*C=(2 : ℂ) • (U*C*U) := by
    have hPM : rootProjection r*(U*U)=rootProjection r := by rw [← mul_assoc,hPU,hPU]
    have hMP : (U*U)*rootProjection r=rootProjection r := by rw [mul_assoc,hUP,hUP]
    rw [hUC]
    dsimp only [C]
    simp only [sub_mul,mul_sub,one_mul,mul_one,hPM,hMP]
    module
  have hshift := gap_shift_posSemidef K r a hr hg
  have hRS : ((D-(2*a : ℂ) • C)*(U*U)+(U*U)*(D-(2*a : ℂ) • C)).PosSemidef := by
    have he : (D-(2*a : ℂ) • C)*(U*U)+(U*U)*(D-(2*a : ℂ) • C)=
        (4 : ℂ) • (U*(K-(a : ℂ) • C)*U) := by
      calc
        _=(D*(U*U)+(U*U)*D)-(2*a : ℂ) • (C*(U*U)+(U*U)*C) := by
          simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,smul_add]; module
        _=_ := by
          rw [hSyl,hCM]
          simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,smul_smul]
          push_cast
          module
    rw [he]
    have hp := hshift.mul_mul_conjTranspose_same U
    rw [hU.eq] at hp
    exact hp.smul (by norm_num : (0 : ℂ) ≤ 4)
  have hDS := sylvester_posSemidef (D-(2*a : ℂ) • C) U V hU hUV hRS
  refine ⟨hD.isHermitian.eq,qform_nonneg_of_posSemidef D hD,hDr,?_⟩
  intro X hX
  have hh := qform_nonneg_of_posSemidef _ hDS X
  have hCX : applySuper C X=X := by
    dsimp only [C]
    rw [applySuper_sub,applySuper_one,applySuper_rootProjection,hX,zero_smul,sub_zero]
  rw [qform,applySuper_sub,applySuper_smul,hCX,hsInner_sub_right,hsInner_smul_right] at hh
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_mul,Complex.ofReal_ofNat,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] at hh
  norm_num [Complex.mul_im,Complex.mul_re] at hh
  change 2*a*hsSq X ≤ qform D X
  exact hh


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma applySuper_ad (H X : Mat ι) : applySuper (ad H) X=H*X-X*H := by
  change act (ad H) X=_
  rw [act_ad]
  rfl

lemma applySuper_pow (T : Super ι) (X : Mat ι) (n : ℕ) :
    applySuper (T^(n+1)) X=applySuper T (applySuper (T^n) X) := by
  rw [pow_succ',applySuper_mul]

lemma ad_hermitian (H : Mat ι) (hH : H.IsHermitian) : (ad H).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  intro x y
  change inner ℂ ((Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) (ad H)) x) y=
    inner ℂ x ((Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) (ad H)) y)
  let X := hsUnvec x
  let Y := hsUnvec y
  have he (Z : EuclideanSpace ℂ (ι × ι)) : hsVec (hsUnvec Z)=Z := hsVec_hsUnvec Z
  have hh : hsInner (applySuper (ad H) X) Y=hsInner X (applySuper (ad H) Y) := by
    rw [applySuper_ad,applySuper_ad,hsInner_sub_left,hsInner_sub_right,
      hsInner_leftMul,hsInner_rightMul,hH.eq]
  simpa only [← hsVec_inner,hsVec_applySuper,X,Y,he] using hh

lemma hermitian_exp_apply_of_preserves (T : Super ι)
    (hT : ∀ X : Mat ι, X.IsHermitian → (applySuper T X).IsHermitian)
    (X : Mat ι) (hX : X.IsHermitian) : (applySuper (mexp T) X).IsHermitian := by
  have hp (n : ℕ) : (applySuper (T^n) X).IsHermitian := by
    induction n with
    | zero => simpa only [pow_zero,applySuper_one] using hX
    | succ n ih => rw [applySuper_pow]; exact hT _ ih
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T).mapL (evalSuper X)
  have ha := hs.map (Matrix.conjTransposeAddEquiv ι ι ℂ).toAddMonoidHom
    (by change Continuous (fun A : Mat ι ↦ Aᴴ); fun_prop)
  change (applySuper (mexp T) X)ᴴ=applySuper (mexp T) X
  apply HasSum.unique ha
  convert! hs using 1
  funext n
  change (applySuper ((n.factorial : ℂ)⁻¹ • T^n) X)ᴴ=
    applySuper ((n.factorial : ℂ)⁻¹ • T^n) X
  rw [applySuper_smul]
  change (((n.factorial : ℂ)⁻¹ • applySuper (T^n) X)ᴴ)=
    (n.factorial : ℂ)⁻¹ • applySuper (T^n) X
  rw [Matrix.conjTranspose_smul,(hp n).eq]
  simp

lemma filtered_hermitian {N : ℕ} (H : Mat ι) (hH : H.IsHermitian)
    (γ : Fin N → Mat ι) (hγ : ∀ i, (γ i).IsHermitian) (β : ℝ) (i : Fin N) :
    (filtered H γ β i).IsHermitian := by
  apply hermitian_exp_apply_of_preserves _ ?_ (γ i) (hγ i)
  intro X hX
  rw [applySuper_smul,applySuper_mul,applySuper_ad,applySuper_ad]
  have hc : star (-(β^2/8 : ℂ))=-(β^2/8 : ℂ) := by simp
  unfold Matrix.IsHermitian
  simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,
    hH.eq,hX.eq,hc]
  noncomm_ring


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def jumpDifference (A : Mat ι) : Super ι :=
  super (fun X ↦ (1/2 : ℂ) • (A*X-X*Aᴴ))

lemma jumpDifference_apply (A X : Mat ι) :
    applySuper (jumpDifference A) X=(1/2 : ℂ) • (A*X-X*Aᴴ) :=
  applySuper_super (((1/2 : ℂ) • (leftAct A-rightAct Aᴴ)).toLinearMap) X

lemma jumpDifference_adjoint_apply (A X : Mat ι) :
    applySuper (jumpDifference A)ᴴ X=(1/2 : ℂ) • (Aᴴ*X-X*A) := by
  have hAdj (Y : Mat ι) :
      hsInner (applySuper (jumpDifference A) Y) X=
        hsInner Y ((1/2 : ℂ) • (Aᴴ*X-X*A)) := by
    rw [jumpDifference_apply,hsInner_smul_left,hsInner_smul_right,hsInner_sub_left,
      hsInner_sub_right,hsInner_leftMul,hsInner_rightMul,Matrix.conjTranspose_conjTranspose]
    norm_num [map_ofNat]
  let F := (1/2 : ℂ) • (Aᴴ*X-X*A)
  let Z := applySuper (jumpDifference A)ᴴ X-F
  have hz : hsInner Z Z=0 := by
    change hsInner Z (applySuper (jumpDifference A)ᴴ X-F)=0
    rw [hsInner_sub_right,← hsInner_applySuper_adjoint,hAdj]
    exact sub_self _
  exact sub_eq_zero.mp ((hsSq_eq_zero_iff Z).mp (congrArg Complex.re hz))

lemma jumpDifference_square_apply (A X : Mat ι) :
    applySuper ((jumpDifference A)ᴴ*jumpDifference A) X=
      (1/4 : ℂ) • (Aᴴ*A*X+X*(Aᴴ*A)-Aᴴ*X*Aᴴ-A*X*A) := by
  rw [applySuper_mul,jumpDifference_apply,jumpDifference_adjoint_apply]
  simp only [mul_smul_comm,smul_mul_assoc,smul_sub,smul_smul]
  noncomm_ring <;> module

lemma filteredK_apply {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (X : Mat (SiteHilbert N)) :
    applySuper (filteredK Q w β) X=(1/4 : ℂ) •
      ((∑ i, (jump (hamiltonian Q w) Q.γ β i)ᴴ*jump (hamiltonian Q w) Q.γ β i)*X+
        X*(∑ i, (jump (hamiltonian Q w) Q.γ β i)ᴴ*jump (hamiltonian Q w) Q.γ β i)-
        ∑ i, ((jump (hamiltonian Q w) Q.γ β i)ᴴ*X*(jump (hamiltonian Q w) Q.γ β i)ᴴ+
          jump (hamiltonian Q w) Q.γ β i*X*jump (hamiltonian Q w) Q.γ β i)) := by
  have hc (i : Fin N) : cfMap Q w β i=jumpDifference (jump (hamiltonian Q w) Q.γ β i) := rfl
  unfold filteredK
  rw [← evalSuper_apply,map_sum]
  simp only [evalSuper_apply,hc,jumpDifference_square_apply,← Finset.smul_sum,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  module

lemma mexp_posSemidef (H : Mat ι) (hH : H.IsHermitian) (s : ℝ) :
    (mexp ((s : ℂ) • H)).PosSemidef := by
  have he : mexp ((s : ℂ) • H)=
      (mexp (((s/2 : ℝ) : ℂ) • H))ᴴ*mexp (((s/2 : ℝ) : ℂ) • H) := by
    rw [(mexp_hermitian H hH (s/2)).eq,mexp_smul_add]
    congr 2
    push_cast
    ring
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma mexp_add_one_invertible (H : Mat ι) (hH : H.IsHermitian) (s : ℝ) :
    (mexp ((s : ℂ) • H)+1)*(mexp ((s : ℂ) • H)+1)⁻¹=1 := by
  have hp := Matrix.PosDef.posSemidef_add (mexp_posSemidef H hH s)
    (Matrix.PosDef.one (n := ι) (R := ℂ))
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit)


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma lindblad_apply {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (β : ℝ) (X : Mat ι) :
    applySuper (lindblad H γ β) X=
      (-Complex.I) • (correction H γ β*X-X*correction H γ β)+
      ∑ i, jump H γ β i*X*(jump H γ β i)ᴴ-
      (1/2 : ℂ) • ((∑ i, (jump H γ β i)ᴴ*jump H γ β i)*X+
        X*(∑ i, (jump H γ β i)ᴴ*jump H γ β i)) := by
  let A := jump H γ β
  let R := correction H γ β
  let F : Mat ι →L[ℂ] Mat ι :=
    (-Complex.I) • (leftAct R-rightAct R)+
      ∑ i, ((rightAct (A i)ᴴ).comp (leftAct (A i))-
        (1/2 : ℂ) • (leftAct ((A i)ᴴ*A i)+rightAct ((A i)ᴴ*A i)))
  have he := applySuper_super F.toLinearMap X
  have hsuper : super F.toLinearMap=lindblad H γ β := by
    congr 1
    funext Y
    change F Y=_
    simp only [F,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,_root_.smul_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,leftAct_apply,rightAct_apply,
      lindblad,anticomm]
    rfl
  rw [hsuper] at he
  rw [he]
  change F X=_
  simp only [F,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,_root_.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,leftAct_apply,rightAct_apply,
    ← Finset.smul_sum,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  dsimp only [A,R]
  abel

lemma balanced_action (B C R S W J X : Mat ι) (hBC : B*C=1) (hCB : C*B=1)
    (hp : Complex.I • R+(1/2 : ℂ) • S=W)
    (hm : (-Complex.I) • R+(1/2 : ℂ) • S=B*B*W*C*C) :
    -(B*((-Complex.I) • (R*(C*X*C)-(C*X*C)*R)+J-
      (1/2 : ℂ) • (S*(C*X*C)+(C*X*C)*S))*B)=
      (B*W*C)*X+X*(B*W*C)-B*J*B := by
  have hBCX (Z : Mat ι) : B*(C*Z)=Z := by rw [← mul_assoc,hBC,one_mul]
  have hCBX (Z : Mat ι) : C*(B*Z)=Z := by rw [← mul_assoc,hCB,one_mul]
  calc
    _=B*(Complex.I • R+(1/2 : ℂ) • S)*C*X+
        X*C*((-Complex.I) • R+(1/2 : ℂ) • S)*B-B*J*B := by
      simp only [mul_add,mul_sub,add_mul,sub_mul,mul_smul_comm,smul_mul_assoc,
        smul_add,smul_sub,neg_smul,smul_neg,mul_neg,neg_mul,mul_assoc,hBCX,hCBX,hBC,hCB,mul_one,one_mul]
      noncomm_ring <;> module
    _=_ := by
      rw [hp,hm]
      simp only [mul_assoc,hBCX,hCBX,hBC,hCB,mul_one,one_mul]

lemma correction_balance {N : ℕ} (H : Mat ι) (hH : H.IsHermitian)
    (γ : Fin N → Mat ι) (β : ℝ) :
    let E := mexp (((β/2 : ℝ) : ℂ) • ad H)
    let S := ∑ i, (jump H γ β i)ᴴ*jump H γ β i
    let W := applySuper (E+1)⁻¹ S
    Complex.I • correction H γ β+(1/2 : ℂ) • S=W ∧
      (-Complex.I) • correction H γ β+(1/2 : ℂ) • S=applySuper E W := by
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
  let E := mexp ((β/2 : ℂ) • ad H)
  let S := ∑ i, (jump H γ β i)ᴴ*jump H γ β i
  let W := applySuper (E+1)⁻¹ S
  have hInv : (E+1)*(E+1)⁻¹=1 := by
    simpa only [E,Complex.ofReal_div,Complex.ofReal_ofNat] using
      mexp_add_one_invertible (ad H) (ad_hermitian H hH) (β/2)
  have hS : S=applySuper E W+W := by
    have hh := congrArg (fun T : Super ι ↦ applySuper T S) hInv
    rw [applySuper_one,applySuper_mul,applySuper_add,applySuper_one] at hh
    exact hh.symm
  have hR : correction H γ β=(Complex.I/2) • (applySuper E W-W) := by
    change (Complex.I/2) • applySuper ((E-1)*(E+1)⁻¹) S=_
    rw [applySuper_mul,applySuper_sub,applySuper_one]
  change Complex.I • correction H γ β+(1/2 : ℂ) • S=W ∧
      (-Complex.I) • correction H γ β+(1/2 : ℂ) • S=applySuper E W
  rw [hR,hS]
  constructor <;> simp only [smul_smul,smul_add,smul_sub] <;>
    norm_num [Complex.I_mul_I,Complex.I_sq,← mul_div_assoc] <;> module


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma jump_adjoint {N : ℕ} (H : Mat ι) (hH : H.IsHermitian) (γ : Fin N → Mat ι)
    (hγ : ∀ i, (γ i).IsHermitian) (β : ℝ) (i : Fin N) :
    (jump H γ β i)ᴴ=mexp (((β/4 : ℝ) : ℂ) • H)*filtered H γ β i*
      mexp (((-(β/4) : ℝ) : ℂ) • H) := by
  unfold jump
  simp only [Matrix.conjTranspose_mul]
  have hB := (mexp_hermitian H hH (β/4)).eq
  have hC := (mexp_hermitian H hH (-(β/4))).eq
  have hY := (filtered_hermitian H hH γ hγ β i).eq
  simp only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] at hB hC ⊢
  rw [hB,hC,hY,mul_assoc]

lemma jump_gibbsRoot_balance {N : ℕ} (H : Mat ι) (hH : H.IsHermitian)
    (γ : Fin N → Mat ι) (hγ : ∀ i, (γ i).IsHermitian) (β : ℝ) (i : Fin N) :
    jump H γ β i*gibbsRoot H β=gibbsRoot H β*(jump H γ β i)ᴴ := by
  rw [jump_adjoint H hH γ hγ β i]
  let B := mexp (((β/4 : ℝ) : ℂ) • H)
  let C := mexp (((-(β/4) : ℝ) : ℂ) • H)
  let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
  have hBR : B*R=C := by
    dsimp only [B,R,C]
    rw [mexp_smul_add]
    congr 2
    push_cast
    ring
  have hRB : R*B=C := by
    dsimp only [B,R,C]
    rw [mexp_smul_add]
    congr 2
    push_cast
    ring
  have hj : jump H γ β i=C*filtered H γ β i*B := by
    simp only [jump,B,C,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  rw [hj]
  unfold gibbsRoot
  rw [mul_smul_comm,smul_mul_assoc]
  congr 1
  suffices he : (C*filtered H γ β i*B)*R=R*(B*filtered H γ β i*C) by
    simpa only [B,C,R,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] using he
  calc
    _=C*filtered H γ β i*(B*R) := by noncomm_ring
    _=C*filtered H γ β i*C := by rw [hBR]
    _=R*(B*filtered H γ β i*C) := by rw [← mul_assoc,← mul_assoc,hRB]

lemma gibbsRoot_ad_exp_fixed (H : Mat ι) (β s : ℝ) :
    applySuper (mexp ((s : ℂ) • ad H)) (gibbsRoot H β)=gibbsRoot H β := by
  rw [exp_ad_apply]
  unfold gibbsRoot
  rw [mul_smul_comm,smul_mul_assoc]
  congr 1
  rw [mexp_smul_add,mexp_smul_add]
  congr 2
  push_cast
  ring

lemma filteredK_root {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) :
    applySuper (filteredK Q w β) (gibbsRoot (hamiltonian Q w) β)=0 := by
  apply (applySuper_sum_adj_mul_eq_zero_iff (cfMap Q w β) _).mpr
  intro i
  change applySuper (jumpDifference (jump (hamiltonian Q w) Q.γ β i)) _=0
  rw [jumpDifference_apply,jump_gibbsRoot_balance (hamiltonian Q w)
    (hamiltonian_hermitian_words Q w) Q.γ Q.car.herm β i,sub_self,smul_zero]


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma conjugate_drift {I : Type} [Fintype I] (B C Z X : Mat ι) (Y : I → Mat ι)
    (hBC : B*C=1) (hCB : C*B=1) :
    B*(Z*(C*X*B)+(C*X*B)*Z-∑ i, Y i*(C*X*B)*Y i)*C=
      (B*Z*C)*X+X*(B*Z*C)-∑ i, (B*Y i*C)*X*(B*Y i*C) := by
  have hBCX (T : Mat ι) : B*(C*T)=T := by rw [← mul_assoc,hBC,one_mul]
  have hCBX (T : Mat ι) : C*(B*T)=T := by rw [← mul_assoc,hCB,one_mul]
  simp only [mul_add,mul_sub,add_mul,sub_mul,Finset.mul_sum,Finset.sum_mul,
    mul_assoc,hBCX,hCBX,hBC,hCB,mul_one,one_mul]

lemma discriminant_balanced_form {N : ℕ} (H : Mat ι) (hH : H.IsHermitian)
    (γ : Fin N → Mat ι) (hγ : ∀ i, (γ i).IsHermitian) (β : ℝ) :
    let B := mexp (((β/4 : ℝ) : ℂ) • H)
    let C := mexp (((-(β/4) : ℝ) : ℂ) • H)
    ∃ Z : Mat ι,
      B*Z*C+C*Z*B=∑ i, (jump H γ β i)ᴴ*jump H γ β i ∧
      ∀ X, applySuper (discriminant H γ β) X=
        Z*X+X*Z-∑ i, filtered H γ β i*X*filtered H γ β i := by
  simp only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  let B := mexp ((β/4 : ℂ) • H)
  let C := mexp ((-(β/4) : ℂ) • H)
  let E := mexp ((β/2 : ℂ) • ad H)
  let S := ∑ i, (jump H γ β i)ᴴ*jump H γ β i
  let W := applySuper (E+1)⁻¹ S
  have hBC : B*C=1 := by
    exact mexp_smul_cancel H (β/4)
  have hCB : C*B=1 := mul_eq_one_comm.mp hBC
  have hBCX (X : Mat ι) : B*(C*X)=X := by rw [← mul_assoc,hBC,one_mul]
  have hCBX (X : Mat ι) : C*(B*X)=X := by rw [← mul_assoc,hCB,one_mul]
  have hE (X : Mat ι) : applySuper E X=B*B*X*C*C := by
    dsimp only [E]
    rw [exp_ad_apply]
    have hBB : B*B=mexp ((β/2 : ℂ) • H) := by
      dsimp only [B]
      rw [mexp_smul_add]
      congr 2
      push_cast
      ring
    have hCC : C*C=mexp ((-(β/2) : ℂ) • H) := by
      dsimp only [C]
      rw [mexp_smul_add]
      congr 2
      push_cast
      ring
    rw [hBB,mul_assoc _ _ C, hCC]
  have hcor := correction_balance H hH γ β
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat] at hcor
  change Complex.I • correction H γ β+(1/2 : ℂ) • S=W ∧
    (-Complex.I) • correction H γ β+(1/2 : ℂ) • S=applySuper E W at hcor
  have hS : applySuper E W+W=S := by
    rw [← hcor.2,← hcor.1]
    module
  have hj (i : Fin N) : jump H γ β i=C*filtered H γ β i*B := by
    simp only [jump,B,C,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  have hjs (i : Fin N) : (jump H γ β i)ᴴ=B*filtered H γ β i*C := by
    simpa only [B,C,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] using
      jump_adjoint H hH γ hγ β i
  refine ⟨B*W*C,?_,?_⟩
  · change B*(B*W*C)*C+C*(B*W*C)*B=S
    rw [hE] at hS
    simpa only [mul_assoc,hBCX,hCBX,hBC,hCB,mul_one,one_mul,add_comm] using hS
  · intro X
    rw [discriminant_similarity,applySuper_neg,applySuper_mul,applySuper_mul,
      applySuper_sandwich,applySuper_sandwich,lindblad_apply]
    simp only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
    change -(B*((-Complex.I) • (correction H γ β*(C*X*C)-(C*X*C)*correction H γ β)+
      (∑ i, jump H γ β i*(C*X*C)*(jump H γ β i)ᴴ)-
        (1/2 : ℂ) • (S*(C*X*C)+(C*X*C)*S))*B)=_
    rw [balanced_action B C (correction H γ β) S W _ X hBC hCB hcor.1 (by rw [← hE]; exact hcor.2)]
    have hJ : B*(∑ i, jump H γ β i*(C*X*C)*(jump H γ β i)ᴴ)*B=
        ∑ i, filtered H γ β i*X*filtered H γ β i := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hjs,hj]
      simp only [mul_assoc,hBCX,hCBX,hBC,hCB,mul_one,one_mul]
    rw [hJ]

lemma discriminant_sylvester {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) :
    let U := mexp (((β/4 : ℝ) : ℂ) • ad (hamiltonian Q w))
    discriminant (hamiltonian Q w) Q.γ β*(U*U)+
      (U*U)*discriminant (hamiltonian Q w) Q.γ β=
      (4 : ℂ) • (U*filteredK Q w β*U) := by
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
  let H := hamiltonian Q w
  let U := mexp ((β/4 : ℂ) • ad H)
  let V := mexp ((-(β/4) : ℂ) • ad H)
  let B := mexp ((β/4 : ℂ) • H)
  let C := mexp ((-(β/4) : ℂ) • H)
  let D := discriminant H Q.γ β
  let K := filteredK Q w β
  have hUV : U*V=1 := mexp_smul_cancel (ad H) (β/4)
  have hVU : V*U=1 := mul_eq_one_comm.mp hUV
  have hBC : B*C=1 := mexp_smul_cancel H (β/4)
  have hCB : C*B=1 := mul_eq_one_comm.mp hBC
  have hU (X : Mat (SiteHilbert N)) : applySuper U X=B*X*C := exp_ad_apply H X (β/4)
  have hV (X : Mat (SiteHilbert N)) : applySuper V X=C*X*B := by
    simpa only [neg_neg] using exp_ad_apply H X (-(β/4))
  have hform := discriminant_balanced_form H (hamiltonian_hermitian_words Q w) Q.γ Q.car.herm β
  simp only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] at hform
  obtain ⟨Z,hZ,hD⟩ := hform
  change B*Z*C+C*Z*B=(∑ i, (jump H Q.γ β i)ᴴ*jump H Q.γ β i) at hZ
  have hj (i : Fin N) : jump H Q.γ β i=C*filtered H Q.γ β i*B := rfl
  have hjs (i : Fin N) : (jump H Q.γ β i)ᴴ=B*filtered H Q.γ β i*C := by
    simpa only [B,C,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] using
      jump_adjoint H (hamiltonian_hermitian_words Q w) Q.γ Q.car.herm β i
  have hconj : U*D*V+V*D*U=(4 : ℂ) • K := by
    apply applySuper_ext
    intro X
    rw [applySuper_add,applySuper_mul,applySuper_mul,applySuper_mul,applySuper_mul,
      hV,hU,hD,hD,hU,hV,
      conjugate_drift B C Z X (filtered H Q.γ β) hBC hCB,
      conjugate_drift C B Z X (filtered H Q.γ β) hCB hBC,
      applySuper_smul]
    have he := filteredK_apply Q w β X
    change applySuper K X=(1/4 : ℂ) •
      ((∑ i, (jump H Q.γ β i)ᴴ*jump H Q.γ β i)*X+
        X*(∑ i, (jump H Q.γ β i)ᴴ*jump H Q.γ β i)-
        ∑ i, ((jump H Q.γ β i)ᴴ*X*(jump H Q.γ β i)ᴴ+
          jump H Q.γ β i*X*jump H Q.γ β i)) at he
    rw [he,smul_smul]
    norm_num
    rw [← hZ]
    simp only [← hj,← hjs,mul_add,add_mul,Finset.sum_add_distrib]
    abel
  change D*(U*U)+(U*U)*D=(4 : ℂ) • (U*K*U)
  have he := congrArg (fun T : Super (SiteHilbert N) ↦ U*T*U) hconj
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc] at he
  have hUVX (T : Super (SiteHilbert N)) : U*(V*T)=T := by rw [← mul_assoc,hUV,one_mul]
  have hVUX (T : Super (SiteHilbert N)) : V*(U*T)=T := by rw [← mul_assoc,hVU,one_mul]
  simpa only [mul_assoc,hUVX,hVUX,hUV,hVU,mul_one,one_mul,add_comm] using he


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma hsSq_smul (z : ℂ) (X : Mat ι) : hsSq (z • X)=‖z‖^2*hsSq X := by
  rw [← hsVec_norm_sq, hsVec_smul, norm_smul, mul_pow, hsVec_norm_sq]

lemma gibbsRoot_hsSq_one [Nonempty ι] (H : Mat ι) (hH : H.IsHermitian) (β : ℝ) :
    hsSq (gibbsRoot H β)=1 := by
  let Z := (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re
  let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
  have hZ : 0 < Z := mexp_trace_pos H hH (-β)
  have hr : gibbsRoot H β=((Real.sqrt Z : ℂ))⁻¹ • R := by
    simp only [gibbsRoot, Z, R, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [hr, hsSq_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hR : hsSq R=Z := mexp_half_hsSq H hH β
  rw [hR]
  calc
    (Real.sqrt Z)⁻¹^2 * Z=Z/(Real.sqrt Z)^2 := by rw [inv_pow]; ring
    _ = 1 := by rw [Real.sq_sqrt hZ.le, div_self hZ.ne']


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

end SYKFastMix.FastMixing
open SYKFastMix.FastMixing
theorem solution {N : ℕ} (Q : Model N) (w : Disorder N) (β a : ℝ)
    (_hβ : 0 ≤ β) (_ha : 0 < a)
    (hform : ∀ X, hsInner (gibbsRoot (hamiltonian Q w) β) X=0 →
      a*hsSq X ≤ qform (filteredK Q w β) X) :
    HasGap (discriminant (hamiltonian Q w) Q.γ β) (gibbsRoot (hamiltonian Q w) β) (2*a) := by
  let H := hamiltonian Q w
  let U := mexp (((β/4 : ℝ) : ℂ) • ad H)
  let V := mexp (((-(β/4) : ℝ) : ℂ) • ad H)
  have hH : H.IsHermitian := hamiltonian_hermitian_words Q w
  have hU : U.IsHermitian := mexp_hermitian (ad H) (ad_hermitian H hH) (β/4)
  have hUV : U*V=1 := by
    simpa only [U,V,Complex.ofReal_neg] using mexp_smul_cancel (ad H) (((β/4 : ℝ) : ℂ))
  have hUr : applySuper U (gibbsRoot H β)=gibbsRoot H β := gibbsRoot_ad_exp_fixed H β (β/4)
  have hK : HasGap (filteredK Q w β) (gibbsRoot H β) a := by
    refine ⟨?_,?_,filteredK_root Q w β,hform⟩
    · unfold filteredK
      simp only [Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    · intro X
      rw [filteredK,qform_sum_adj_mul]
      exact Finset.sum_nonneg (fun i hi ↦ hsSq_nonneg _)
  exact sylvester_gap (filteredK Q w β) (discriminant H Q.γ β) U V (gibbsRoot H β) a
    (gibbsRoot_hsSq_one H hH β) hK hU hUV hUr (discriminant_sylvester Q w β)


namespace SYKFastMix.FastMixing

end SYKFastMix.FastMixing
end
