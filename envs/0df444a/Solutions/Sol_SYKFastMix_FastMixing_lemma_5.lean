-- Prove2me | solution 1 for SYKFastMix.FastMixing.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:23:50.839203+00:00
-- url     : https://prove2.me/submissions/a2dbeca0-8d6b-421c-aa1e-2ea38fea21cb

import Mathlib
import Theorems.Thm_SYKFastMix_FastMixing_lemma_4

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder NNReal ENNReal

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

def familyVec {I : Type} (F : I → Mat ι) : EuclideanSpace ℂ (I × (ι × ι)) :=
  WithLp.toLp 2 (fun p ↦ opVec (F p.1) p.2)

lemma familyVec_sub {I : Type} (F G : I → Mat ι) :
    familyVec (fun i ↦ F i - G i) = familyVec F - familyVec G := by
  apply PiLp.ext
  intro p
  rfl

lemma familyVec_add {I : Type} (F G : I → Mat ι) :
    familyVec (fun i ↦ F i + G i) = familyVec F + familyVec G := by
  apply PiLp.ext
  intro p
  rfl

lemma familyVec_eq_zero_iff {I : Type} (F : I → Mat ι) :
    familyVec F = 0 ↔ ∀ i, F i = 0 := by
  constructor
  · intro h i
    ext a b
    have hp := congrArg (fun v : EuclideanSpace ℂ (I × (ι × ι)) ↦ v (i, (a, b))) h
    exact hp
  · intro h
    apply PiLp.ext
    intro p
    change opVec (F p.1) p.2 = 0
    rw [h p.1]
    rfl

lemma familyVec_norm_sq {I : Type} [Fintype I] (F : I → Mat ι) :
    ‖familyVec F‖ ^ 2 = ∑ i, hsSq (F i) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [familyVec, hsSq_eq_sum_norm_sq]
  rw [← Finset.univ_product_univ, Finset.sum_product]

lemma familyVec_norm {I : Type} [Fintype I] (F : I → Mat ι) :
    ‖familyVec F‖ = Real.sqrt (∑ i, hsSq (F i)) := by
  rw [← familyVec_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm


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

lemma euclideanAct_exp (T : Super ι) :
    Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) (mexp T) =
      NormedSpace.exp (Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) T) := by
  letI : NormedAlgebra ℚ (Super ι) := .restrictScalars ℚ ℂ (Super ι)
  exact NormedSpace.map_exp (Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ))
    (Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional T


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


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

lemma hermitian_repr_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Mat ι) (hA : A.IsHermitian) (x : EuclideanSpace ℂ ι) (i : ι) :
    hA.eigenvectorBasis.repr ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x) i =
      (hA.eigenvalues i : ℂ) * hA.eigenvectorBasis.repr x i := by
  have he : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (hA.eigenvectorBasis i) =
      (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    change (A *ᵥ (hA.eigenvectorBasis i : ι → ℂ)) j = _
    rw [hA.mulVec_eigenvectorBasis]
    rfl
  have hs := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (hA.eigenvectorBasis i) x
  change inner ℂ ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (hA.eigenvectorBasis i)) x =
    inner ℂ (hA.eigenvectorBasis i) ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x) at hs
  simp only [OrthonormalBasis.repr_apply_apply]
  rw [← hs, he, inner_smul_left]
  simp

lemma repr_exp_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℂ)
    (hdiag : ∀ x i, b.repr (T x) i = ev i * b.repr x i) (x : E) (i : ι) :
    b.repr ((NormedSpace.exp T) x) i = Complex.exp (ev i) * b.repr x i := by
  let L : (E →L[ℂ] E) →L[ℂ] ℂ := {
    toFun := fun U ↦ b.repr (U x) i
    map_add' := by intro U V; simp
    map_smul' := by intro z U; simp
    cont := by fun_prop }
  have hp (n : ℕ) : L (T^n) = (ev i)^n * b.repr x i := by
    induction n with
    | zero => simp [L]
    | succ n ih =>
      change b.repr ((T^(n+1)) x) i = _
      rw [pow_succ', ContinuousLinearMap.mul_apply, hdiag]
      change ev i * L (T^n) = _
      rw [ih, pow_succ]
      ring
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T).mapL L
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (ev i)).mul_right (b.repr x i)
  apply HasSum.unique h
  convert! hscalar using 1
  · funext n
    rw [map_smul, hp]
    simp only [smul_eq_mul]
    ring
  · rw [Complex.exp_eq_exp_ℂ]


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma basis_unitary_coordinate (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℝ)
    (hd : ∀ x i, b.repr (T x) i=(ev i : ℂ)*b.repr x i) (x : E) (s : ℝ) (i : ι) :
    b.repr ((NormedSpace.exp (((s : ℂ)*Complex.I) • T)) x) i=
      Complex.exp ((s : ℂ)*Complex.I*(ev i : ℂ))*b.repr x i := by
  apply repr_exp_apply b (((s : ℂ)*Complex.I) • T) (fun i ↦ (s : ℂ)*Complex.I*(ev i : ℂ))
  intro y j
  change b.repr (((s : ℂ)*Complex.I) • T y) j=_
  simp only [map_smul,PiLp.smul_apply,smul_eq_mul,hd,mul_assoc]

lemma basis_unitary_norm (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℝ)
    (hd : ∀ x i, b.repr (T x) i=(ev i : ℂ)*b.repr x i) (x : E) (s : ℝ) :
    ‖(NormedSpace.exp (((s : ℂ)*Complex.I) • T)) x‖=‖x‖ := by
  have hs : ‖(NormedSpace.exp (((s : ℂ)*Complex.I) • T)) x‖^2=‖x‖^2 := by
    rw [← b.repr.norm_map ((NormedSpace.exp (((s : ℂ)*Complex.I) • T)) x),
      ← b.repr.norm_map x,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    rw [basis_unitary_coordinate b T ev hd,norm_mul,Complex.norm_exp]
    have hz : ((s : ℂ)*Complex.I*(ev i : ℂ)).re=0 := by simp [Complex.mul_re,Complex.mul_im]
    rw [hz,Real.exp_zero,one_mul]
  nlinarith [norm_nonneg ((NormedSpace.exp (((s : ℂ)*Complex.I) • T)) x),norm_nonneg x]

lemma integrable_basis_unitary_orbit (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℝ)
    (hd : ∀ x i, b.repr (T x) i=(ev i : ℂ)*b.repr x i) (x : E)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun s : ℝ ↦ (NormedSpace.exp (((s : ℂ)*Complex.I) • T)) x) μ := by
  letI : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  have hc : Continuous (fun s : ℝ ↦ (NormedSpace.exp (((s : ℂ)*Complex.I) • T)) x) := by fun_prop
  exact (integrable_const ‖x‖).mono' hc.aestronglyMeasurable
    (ae_of_all _ (fun s ↦ (basis_unitary_norm b T ev hd x s).le))

lemma basis_gaussian_filter (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℝ)
    (hd : ∀ x i, b.repr (T x) i=(ev i : ℂ)*b.repr x i) (x : E) (v : ℝ≥0) :
    (∫ s : ℝ, (NormedSpace.exp (((s : ℂ)*Complex.I) • T)) x ∂gaussianReal 0 v)=
      (NormedSpace.exp ((-((v : ℝ)/2) : ℂ) • (T*T))) x := by
  have hint := integrable_basis_unitary_orbit b T ev hd x (gaussianReal 0 v)
  apply b.repr.injective
  apply PiLp.ext
  intro i
  let L : E →L[ℂ] ℂ := {
    toFun y := b.repr y i
    map_add' y z := by simp
    map_smul' z y := by simp
    cont := by fun_prop }
  have hdiag : ∀ y j, b.repr (((-((v : ℝ)/2) : ℂ) • (T*T)) y) j=
      ((-((v : ℝ)/2) : ℂ)*(ev j : ℂ)^2)*b.repr y j := by
    intro y j
    change b.repr ((-((v : ℝ)/2) : ℂ) • T (T y)) j=_
    simp only [map_smul,PiLp.smul_apply,smul_eq_mul,hd]
    ring
  rw [repr_exp_apply b _ (fun j ↦ (-((v : ℝ)/2) : ℂ)*(ev j : ℂ)^2) hdiag]
  change L (∫ s : ℝ, (NormedSpace.exp (((s : ℂ)*Complex.I) • T)) x ∂gaussianReal 0 v)=_
  rw [← L.integral_comp_comm hint]
  change (∫ s : ℝ, b.repr ((NormedSpace.exp (((s : ℂ)*Complex.I) • T)) x) i ∂gaussianReal 0 v)=_
  simp_rw [basis_unitary_coordinate b T ev hd]
  rw [integral_mul_const]
  have hchar : (∫ s : ℝ, Complex.exp ((s : ℂ)*Complex.I*(ev i : ℂ)) ∂gaussianReal 0 v)=
      Complex.exp ((-((v : ℝ)/2) : ℂ)*(ev i : ℂ)^2) := by
    have he := charFun_gaussianReal (μ := 0) (v := v) (ev i)
    rw [charFun_apply_real] at he
    convert! he using 1
    · congr 1
      funext s
      congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  rw [hchar]


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_sub_initial_le_exp_nonneg (f f' : ℝ → E) (m : ℝ) (hm : 0 < m)
    (hf : ∀ s, HasDerivAt f (f' s) s) (hb : ∀ s, ‖f' s‖ ≤ m*‖f s‖)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖f t-f 0‖ ≤ (Real.exp (m*t)-1)*‖f 0‖ := by
  let g := fun s ↦ f s-f 0
  have hg (s : ℝ) : HasDerivAt g (f' s) s := (hf s).sub_const (f 0)
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun s ↦ (hg s).continuousAt)
  have hbound (s : ℝ) : ‖f' s‖ ≤ m*‖g s‖+m*‖f 0‖ := by
    calc
      _ ≤ m*‖f s‖ := hb s
      _ ≤ m*(‖f s-f 0‖+‖f 0‖) := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add _ _) hm.le
      _ = _ := by dsimp only [g]; ring
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := g) (f' := f') (δ := 0) (K := m) (ε := m*‖f 0‖)
    (a := 0) (b := t) hc.continuousOn
    (fun s hs ↦ (hg s).hasDerivWithinAt)
    (by simp [g]) (fun s hs ↦ hbound s) t ⟨ht,le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hm.ne'] at hh
  simpa only [g,zero_mul,zero_add,zero_div,sub_zero,mul_div_cancel_left₀ _ hm.ne',mul_comm] using hh

lemma norm_sub_initial_le_exp_abs (f f' : ℝ → E) (m : ℝ) (hm : 0 < m)
    (hf : ∀ s, HasDerivAt f (f' s) s) (hb : ∀ s, ‖f' s‖ ≤ m*‖f s‖) (t : ℝ) :
    ‖f t-f 0‖ ≤ (Real.exp (m*|t|)-1)*‖f 0‖ := by
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using norm_sub_initial_le_exp_nonneg f f' m hm hf hb t ht
  · have hnt : 0 ≤ -t := by linarith
    have hd (s : ℝ) : HasDerivAt (fun u ↦ f (-u)) (-f' (-s)) s := by
      simpa only [neg_one_smul,Function.comp_def] using! (hf (-s)).scomp s (hasDerivAt_neg s)
    have hbn (s : ℝ) : ‖-f' (-s)‖ ≤ m*‖f (-s)‖ := by rw [norm_neg]; exact hb (-s)
    have hh := norm_sub_initial_le_exp_nonneg (fun s ↦ f (-s)) (fun s ↦ -f' (-s)) m hm hd hbn (-t) hnt
    simpa only [neg_neg,neg_zero,abs_of_neg (lt_of_not_ge ht)] using hh


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma complex_derivative_real_parameter {f : ℂ → F} {f' : F} (s : ℝ)
    (hf : HasDerivAt f f' (s : ℂ)) : HasDerivAt (fun t : ℝ ↦ f (t : ℂ)) f' s := by
  have he := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s
    (Complex.ofRealCLM.hasFDerivAt.hasDerivAt)
  convert! he using 1 <;> simp

def imaginaryEvolution (T : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  NormedSpace.exp (z • (Complex.I • T))

lemma imaginaryEvolution_real (T : E →L[ℂ] E) (s : ℝ) :
    imaginaryEvolution T (s : ℂ)=NormedSpace.exp (((s : ℂ)*Complex.I) • T) := by
  rw [imaginaryEvolution,smul_smul]

lemma imaginaryEvolution_derivative (T : E →L[ℂ] E) (z : ℂ) :
    HasDerivAt (imaginaryEvolution T) (Complex.I • (T*imaginaryEvolution T z)) z := by
  simpa only [imaginaryEvolution,smul_mul_assoc] using!
    hasDerivAt_exp_smul_const' (Complex.I • T) z

lemma imaginaryEvolution_commute (T : E →L[ℂ] E) (z : ℂ) (x : E) :
    T (imaginaryEvolution T z x)=imaginaryEvolution T z (T x) := by
  letI : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
  have hc : Commute T (z • (Complex.I • T)) := ((Commute.refl T).smul_right Complex.I).smul_right z
  have he := congrArg (fun L : E →L[ℂ] E ↦ L x) hc.exp_right.eq
  exact he

def relativeOrbit (S : F →L[ℂ] F) (T : E →L[ℂ] E) (C : E →L[ℂ] F) (x : E) (z : ℂ) : F :=
  imaginaryEvolution S z (C (imaginaryEvolution T (-z) x))

lemma relativeOrbit_complex_derivative (S : F →L[ℂ] F) (T : E →L[ℂ] E)
    (C : E →L[ℂ] F) (M : F →L[ℂ] F)
    (hrel : ∀ y, C (T y)-S (C y)=M (C y)) (x : E) (z : ℂ) :
    HasDerivAt (relativeOrbit S T C x)
      ((-Complex.I) • imaginaryEvolution S z (M (C (imaginaryEvolution T (-z) x)))) z := by
  have hdT := (imaginaryEvolution_derivative T (-z)).scomp z (hasDerivAt_neg z)
  have hdTx := hdT.clm_apply (hasDerivAt_const z x)
  have hdC := (hasDerivAt_const z C).clm_apply hdTx
  have hd := (imaginaryEvolution_derivative S z).clm_apply hdC
  change HasDerivAt (relativeOrbit S T C x) _ z at hd
  convert! hd using 1
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,zero_add,
    _root_.smul_apply,mul_apply_eq_comp,map_smul,neg_one_smul,smul_neg,neg_smul,
    imaginaryEvolution_commute,Function.comp_apply,map_zero,add_zero,map_add]
  have he := congrArg (imaginaryEvolution S z) (hrel (imaginaryEvolution T (-z) x))
  rw [map_sub] at he
  rw [← he]
  simp only [smul_sub,neg_smul,one_smul,_root_.neg_apply,_root_.smul_apply,
    mul_apply_eq_comp,map_neg,map_smul]
  module

lemma relativeOrbit_real_derivative (S : F →L[ℂ] F) (T : E →L[ℂ] E)
    (C : E →L[ℂ] F) (M : F →L[ℂ] F)
    (hrel : ∀ y, C (T y)-S (C y)=M (C y)) (x : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ relativeOrbit S T C x (t : ℂ))
      ((-Complex.I) • imaginaryEvolution S (s : ℂ) (M (C (imaginaryEvolution T (-(s : ℂ)) x)))) s :=
  complex_derivative_real_parameter s (relativeOrbit_complex_derivative S T C M hrel x (s : ℂ))

lemma relativeOrbit_displacement {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : OrthonormalBasis κ ℂ F) (S : F →L[ℂ] F) (ev : κ → ℝ)
    (hd : ∀ y i, b.repr (S y) i=(ev i : ℂ)*b.repr y i)
    (T : E →L[ℂ] E) (C : E →L[ℂ] F) (M : F →L[ℂ] F)
    (hrel : ∀ y, C (T y)-S (C y)=M (C y)) (m : ℝ) (hm : 0 < m) (hM : ‖M‖ ≤ m)
    (x : E) (s : ℝ) :
    ‖relativeOrbit S T C x (s : ℂ)-C x‖ ≤ (Real.exp (m*|s|)-1)*‖C x‖ := by
  let f := fun t : ℝ ↦ relativeOrbit S T C x (t : ℂ)
  let f' := fun t : ℝ ↦ (-Complex.I) • imaginaryEvolution S (t : ℂ)
    (M (C (imaginaryEvolution T (-(t : ℂ)) x)))
  have hf : ∀ t, HasDerivAt f (f' t) t := fun t ↦ relativeOrbit_real_derivative S T C M hrel x t
  have hb (t : ℝ) : ‖f' t‖ ≤ m*‖f t‖ := by
    have hn (y : F) : ‖imaginaryEvolution S (t : ℂ) y‖=‖y‖ := by
      rw [imaginaryEvolution_real]
      exact basis_unitary_norm b S ev hd y t
    change ‖(-Complex.I) • imaginaryEvolution S (t : ℂ) (M (C (imaginaryEvolution T (-(t : ℂ)) x)))‖ ≤
      m*‖imaginaryEvolution S (t : ℂ) (C (imaginaryEvolution T (-(t : ℂ)) x))‖
    rw [norm_smul,norm_neg,Complex.norm_I,one_mul,hn,hn]
    exact (M.le_opNorm _).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  have he := norm_sub_initial_le_exp_abs f f' m hm hf hb s
  have hz : f 0=C x := by simp [f,relativeOrbit,imaginaryEvolution]
  simpa only [hz,f] using he


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def hsUnvecCLM : EuclideanSpace ℂ (ι × ι) →L[ℂ] Mat ι where
  toFun := hsUnvec
  map_add' x y := by ext a b; rfl
  map_smul' z x := by ext a b; rfl
  cont := by unfold hsUnvec; fun_prop

lemma hsUnvec_hsVec (X : Mat ι) : hsUnvec (hsVec X)=X := rfl

lemma unvec_exp_matrix (A : Super ι) (z : ℂ) (X : Mat ι) :
    hsUnvecCLM ((NormedSpace.exp (z • Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) A)) (hsVec X))=
      applySuper (mexp (z • A)) X := by
  rw [← map_smul,← euclideanAct_exp,← hsVec_applySuper]
  rfl

lemma integrable_ad_unitary (H : Mat ι) (hH : H.IsHermitian) (X : Mat ι)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun s : ℝ ↦ applySuper (mexp (((s : ℂ)*Complex.I) • ad H)) X) μ := by
  let T := Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) (ad H)
  have hA := ad_hermitian H hH
  have hi := integrable_basis_unitary_orbit hA.eigenvectorBasis T hA.eigenvalues
    (hermitian_repr_apply (ad H) hA) (hsVec X) μ
  have hh := (hsUnvecCLM (ι := ι)).integrable_comp hi
  simpa only [T,unvec_exp_matrix] using hh

lemma gaussian_ad_filter (H : Mat ι) (hH : H.IsHermitian) (X : Mat ι) (v : ℝ≥0) :
    (∫ s : ℝ, applySuper (mexp (((s : ℂ)*Complex.I) • ad H)) X ∂gaussianReal 0 v)=
      applySuper (mexp ((-((v : ℝ)/2) : ℂ) • (ad H*ad H))) X := by
  let T := Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) (ad H)
  have hA := ad_hermitian H hH
  have hi := integrable_basis_unitary_orbit hA.eigenvectorBasis T hA.eigenvalues
    (hermitian_repr_apply (ad H) hA) (hsVec X) (gaussianReal 0 v)
  have hf := basis_gaussian_filter hA.eigenvectorBasis T hA.eigenvalues
    (hermitian_repr_apply (ad H) hA) (hsVec X) v
  have hh := congrArg (hsUnvecCLM (ι := ι)) hf
  rw [← (hsUnvecCLM (ι := ι)).integral_comp_comm hi] at hh
  simp only [T,← map_mul,unvec_exp_matrix] at hh
  exact hh

lemma ad_filter_imaginary_commute (H : Mat ι) (a b : ℂ) :
    mexp (a • ad H)*mexp (b • (ad H*ad H))=
      mexp (b • (ad H*ad H))*mexp (a • ad H) := by
  letI : NormedAlgebra ℚ (Super ι) := .restrictScalars ℚ ℂ (Super ι)
  have hc : Commute (ad H) (ad H*ad H) := by change ad H*(ad H*ad H)=(ad H*ad H)*ad H; rw [mul_assoc]
  exact ((hc.smul_left a).smul_right b).exp.eq

lemma gaussian_imaginary_filter {N : ℕ} (Q : Model N) (w : Disorder N) (β s : ℝ) (i : Fin N) :
    (∫ t : ℝ, applySuper (mexp (((t : ℂ)*Complex.I) • ad (hamiltonian Q w))) (imaginary Q w s i)
      ∂gaussianReal 0 (Real.toNNReal (β^2/4)))=
      mexp ((-s : ℂ) • hamiltonian Q w)*filtered (hamiltonian Q w) Q.γ β i*
        mexp ((s : ℂ) • hamiltonian Q w) := by
  let H := hamiltonian Q w
  rw [gaussian_ad_filter H (hamiltonian_hermitian_words Q w)]
  have hv : ((Real.toNNReal (β^2/4) : ℝ))=β^2/4 := Real.coe_toNNReal _ (by positivity)
  rw [hv]
  have hi : imaginary Q w s i=applySuper (mexp ((-s : ℂ) • ad H)) (Q.γ i) := by
    rw [exp_ad_apply]
    simp only [neg_neg]
    rfl
  rw [hi,← applySuper_mul,← ad_filter_imaginary_commute,applySuper_mul,exp_ad_apply]
  simp only [neg_neg]
  have hc : (-((β^2/4)/2) : ℂ)=-(β^2/8 : ℂ) := by push_cast; ring
  simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat]
  rw [hc]
  rfl


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

def repeatBlock {I ι : Type} [DecidableEq I] (A : Mat ι) : Mat (I × ι) :=
  Matrix.of (fun p q ↦ if p.1=q.1 then A p.2 q.2 else 0)

lemma repeatBlock_mul {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq I]
    (A B : Mat ι) : repeatBlock (I := I) A * repeatBlock B=repeatBlock (A*B) := by
  ext p q
  simp only [repeatBlock, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hpq : p.1=q.1
  · simp [hpq]
  · simp [hpq]

lemma repeatBlock_one {I ι : Type} [DecidableEq I] [DecidableEq ι] :
    repeatBlock (I := I) (1 : Mat ι)=1 := by
  ext p q
  simp [repeatBlock, Matrix.one_apply, Prod.ext_iff, ite_and]


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {I ι : Type} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

lemma repeatBlock_hermitian (T : Mat ι) (hT : T.IsHermitian) :
    (repeatBlock (I := I) T).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply,repeatBlock,Matrix.of_apply]
  by_cases he : p.1=q.1
  · simp only [he,eq_self_iff_true,ite_true]
    exact congrFun (congrFun hT.eq p.2) q.2
  · simp [he,Ne.symm he]

lemma repeatBlock_familyVec (T : Super ι) (F : I → Mat ι) :
    (Matrix.toEuclideanCLM (n := I × (ι × ι)) (𝕜 := ℂ) (repeatBlock T)) (familyVec F)=
      familyVec (fun i ↦ applySuper T (F i)) := by
  apply PiLp.ext
  intro p
  change (∑ q : I × (ι × ι), (if p.1=q.1 then T p.2 q.2 else 0)*F q.1 q.2.1 q.2.2)=_
  rw [Fintype.sum_prod_type]
  simp only [ite_mul,zero_mul]
  simp
  rfl

def couplingFamilyCLM (C : I → Super ι) :
    EuclideanSpace ℂ (ι × ι) →L[ℂ] EuclideanSpace ℂ (I × (ι × ι)) where
  toFun x := familyVec (fun i ↦ applySuper (C i) (hsUnvec x))
  map_add' x y := by
    apply PiLp.ext
    intro p
    change (act (C p.1)) (hsUnvec x+hsUnvec y) p.2.1 p.2.2=_
    rw [map_add]
    rfl
  map_smul' z x := by
    apply PiLp.ext
    intro p
    change (act (C p.1)) (z • hsUnvec x) p.2.1 p.2.2=_
    rw [map_smul]
    rfl
  cont := by unfold familyVec opVec applySuper hsUnvec; fun_prop

lemma couplingFamilyCLM_hsVec (C : I → Super ι) (X : Mat ι) :
    couplingFamilyCLM C (hsVec X)=familyVec (fun i ↦ applySuper (C i) X) := rfl

lemma blockM_familyVec {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ)
    (F : Fin N → Mat (SiteHilbert N)) :
    (Matrix.toEuclideanCLM (n := Fin N × (SiteHilbert N × SiteHilbert N)) (𝕜 := ℂ)
      (blockM Q w s)) (familyVec F)=
      familyVec (fun i ↦ ∑ j, applySuper (mBlock w (imaginary Q w s) (imaginary Q w (-s))
        (imaginary Q w s) (imaginary Q w (-s)) i j) (F j)) := by
  apply PiLp.ext
  intro p
  change (∑ q : Fin N × (SiteHilbert N × SiteHilbert N),
    blockM Q w s p q*F q.1 q.2.1 q.2.2)=_
  simp only [blockM,Fintype.sum_prod_type,applySuper,familyVec,opVec,Matrix.sum_apply]

lemma block_jump_intertwining {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β) :
    let T := Matrix.toEuclideanCLM (n := SiteHilbert N × SiteHilbert N) (𝕜 := ℂ) (ad (hamiltonian Q w))
    let S := Matrix.toEuclideanCLM (n := Fin N × (SiteHilbert N × SiteHilbert N)) (𝕜 := ℂ)
      (repeatBlock (ad (hamiltonian Q w)))
    let C := couplingFamilyCLM (cMap Q w β)
    let M := Matrix.toEuclideanCLM (n := Fin N × (SiteHilbert N × SiteHilbert N)) (𝕜 := ℂ)
      (blockM Q w (β/4))
    ∀ y, C (T y)-S (C y)=M (C y) := by
  dsimp only
  intro y
  let X := hsUnvec y
  have hy : y=hsVec X := (hsVec_hsUnvec y).symm
  rw [hy,← hsVec_applySuper,couplingFamilyCLM_hsVec,couplingFamilyCLM_hsVec,
    repeatBlock_familyVec,blockM_familyVec,← familyVec_sub]
  apply PiLp.ext
  intro p
  have he := lemma_4 Q w β hβ X p.1
  simpa only [applySuper_ad,familyVec,opVec] using!
    congrArg (fun Y : Mat (SiteHilbert N) ↦ Y p.2.1 p.2.2) he

lemma block_jump_orbit_bound {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β)
    (hM : SYKEdge.opNorm (blockM Q w (β/4)) ≤ 150*Q.J) (X : Mat (SiteHilbert N)) (s : ℝ) :
    let T := Matrix.toEuclideanCLM (n := SiteHilbert N × SiteHilbert N) (𝕜 := ℂ) (ad (hamiltonian Q w))
    let S := Matrix.toEuclideanCLM (n := Fin N × (SiteHilbert N × SiteHilbert N)) (𝕜 := ℂ)
      (repeatBlock (ad (hamiltonian Q w)))
    let C := couplingFamilyCLM (cMap Q w β)
    ‖relativeOrbit S T C (hsVec X) (s : ℂ)-familyVec (fun i ↦ applySuper (cMap Q w β i) X)‖ ≤
      (Real.exp ((150*Q.J)*|s|)-1)*‖familyVec (fun i ↦ applySuper (cMap Q w β i) X)‖ := by
  dsimp only
  let H := hamiltonian Q w
  let A := repeatBlock (I := Fin N) (ad H)
  have hA : A.IsHermitian := repeatBlock_hermitian _ (ad_hermitian H (hamiltonian_hermitian_words Q w))
  have he := relativeOrbit_displacement hA.eigenvectorBasis
    (Matrix.toEuclideanCLM (n := Fin N × (SiteHilbert N × SiteHilbert N)) (𝕜 := ℂ) A)
    hA.eigenvalues (hermitian_repr_apply A hA)
    (Matrix.toEuclideanCLM (n := SiteHilbert N × SiteHilbert N) (𝕜 := ℂ) (ad H))
    (couplingFamilyCLM (cMap Q w β))
    (Matrix.toEuclideanCLM (n := Fin N × (SiteHilbert N × SiteHilbert N)) (𝕜 := ℂ) (blockM Q w (β/4)))
    (block_jump_intertwining Q w β hβ) (150*Q.J) (by have h := Q.positive; positivity) hM (hsVec X) s
  simpa only [couplingFamilyCLM_hsVec] using he


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {I ι : Type} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

def repeatBlockAlgHom : Mat ι →ₐ[ℂ] Mat (I × ι) where
  toFun := repeatBlock
  map_one' := repeatBlock_one
  map_mul' A B := (repeatBlock_mul A B).symm
  map_zero' := by ext p q; simp [repeatBlock]
  map_add' A B := by ext p q; by_cases h : p.1=q.1 <;> simp [repeatBlock,h]
  commutes' z := by
    ext p q
    simp [repeatBlock,Algebra.algebraMap_eq_smul_one,Matrix.one_apply,Prod.ext_iff,ite_and]

lemma repeatBlock_smul (z : ℂ) (A : Mat ι) : repeatBlock (I := I) (z • A)=z • repeatBlock A :=
  (repeatBlockAlgHom (I := I) (ι := ι)).toLinearMap.map_smul z A

lemma repeatBlock_mexp (A : Mat ι) : repeatBlock (I := I) (mexp A)=mexp (repeatBlock A) := by
  letI : NormedAlgebra ℚ (Mat ι) := .restrictScalars ℚ ℂ (Mat ι)
  exact NormedSpace.map_exp (repeatBlockAlgHom (I := I) (ι := ι))
    (repeatBlockAlgHom (I := I) (ι := ι)).toLinearMap.continuous_of_finiteDimensional A

lemma euclidean_matrix_exp (A : Mat ι) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (mexp A)=
      NormedSpace.exp (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) := by
  letI : NormedAlgebra ℚ (Mat ι) := .restrictScalars ℚ ℂ (Mat ι)
  exact NormedSpace.map_exp (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional A

lemma imaginaryEvolution_matrix (A : Mat ι) (s : ℝ) :
    imaginaryEvolution (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (s : ℂ)=
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (mexp (((s : ℂ)*Complex.I) • A)) := by
  rw [imaginaryEvolution_real,euclidean_matrix_exp,map_smul]

lemma block_exp_familyVec (T : Super ι) (z : ℂ) (F : I → Mat ι) :
    (NormedSpace.exp (z • Matrix.toEuclideanCLM (n := I × (ι × ι)) (𝕜 := ℂ) (repeatBlock T))) (familyVec F)=
      familyVec (fun i ↦ applySuper (mexp (z • T)) (F i)) := by
  rw [← map_smul,← euclidean_matrix_exp,← repeatBlock_smul,← repeatBlock_mexp]
  exact repeatBlock_familyVec (mexp (z • T)) F

lemma relativeOrbit_familyVec {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (X : Mat (SiteHilbert N)) (s : ℝ) :
    let T := Matrix.toEuclideanCLM (n := SiteHilbert N × SiteHilbert N) (𝕜 := ℂ) (ad (hamiltonian Q w))
    let S := Matrix.toEuclideanCLM (n := Fin N × (SiteHilbert N × SiteHilbert N)) (𝕜 := ℂ)
      (repeatBlock (ad (hamiltonian Q w)))
    relativeOrbit S T (couplingFamilyCLM (cMap Q w β)) (hsVec X) (s : ℂ)=
      familyVec (fun i ↦ applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w)))
        (applySuper (cMap Q w β i) (applySuper (mexp (((-s : ℂ)*Complex.I) • ad (hamiltonian Q w))) X))) := by
  dsimp only
  unfold relativeOrbit
  have hi : imaginaryEvolution (Matrix.toEuclideanCLM (n := SiteHilbert N × SiteHilbert N) (𝕜 := ℂ)
      (ad (hamiltonian Q w))) (-(s : ℂ))=
      Matrix.toEuclideanCLM (n := SiteHilbert N × SiteHilbert N) (𝕜 := ℂ)
        (mexp (((-s : ℂ)*Complex.I) • ad (hamiltonian Q w))) := by
    simpa only [Complex.ofReal_neg] using imaginaryEvolution_matrix (ad (hamiltonian Q w)) (-s)
  rw [hi]
  rw [← hsVec_applySuper,couplingFamilyCLM_hsVec,imaginaryEvolution_real,block_exp_familyVec]

lemma jump_tuple_displacement {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β)
    (hM : SYKEdge.opNorm (blockM Q w (β/4)) ≤ 150*Q.J) (X : Mat (SiteHilbert N)) (s : ℝ) :
    ‖familyVec (fun i ↦ applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w)))
        (applySuper (cMap Q w β i) (applySuper (mexp (((-s : ℂ)*Complex.I) • ad (hamiltonian Q w))) X)))-
      familyVec (fun i ↦ applySuper (cMap Q w β i) X)‖ ≤
      (Real.exp ((150*Q.J)*|s|)-1)*‖familyVec (fun i ↦ applySuper (cMap Q w β i) X)‖ := by
  have he := block_jump_orbit_bound Q w β hβ hM X s
  dsimp only at he
  rw [relativeOrbit_familyVec] at he
  exact he


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
lemma imaginary_conjTranspose {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) (i : Fin N) :
    (imaginary Q w s i)ᴴ=imaginary Q w (-s) i := by
  unfold imaginary
  simp only [Complex.ofReal_neg, neg_neg]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have hp := mexp_hermitian _ (hamiltonian_hermitian_words Q w) s
  have hn := mexp_hermitian _ (hamiltonian_hermitian_words Q w) (-s)
  simp only [Complex.ofReal_neg] at hn
  rw [hp.eq, hn.eq, (Q.car.herm i).eq]
  simp only [mul_assoc]


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {N : ℕ}
lemma cMap_apply_commutator (Q : Model N) (w : Disorder N) (β : ℝ) (i : Fin N)
    (X : Mat (SiteHilbert N)) :
    applySuper (cMap Q w β i) X=(1/2 : ℂ) •
      (imaginary Q w (β/4) i*X-X*imaginary Q w (-(β/4)) i) := by
  let A := imaginary Q w (β/4) i
  have he := applySuper_super (((1/2 : ℂ) • (leftAct A-rightAct Aᴴ)).toLinearMap) X
  change applySuper (cMap Q w β i) X=(1/2 : ℂ) • (A*X-X*Aᴴ) at he
  rw [he,imaginary_conjTranspose]


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing
variable {ι I Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [MeasurableSpace Ω]

lemma ad_evolution_mul (H X Y : Mat ι) (a : ℂ) :
    applySuper (mexp (a • ad H)) (X*Y)=
      applySuper (mexp (a • ad H)) X*applySuper (mexp (a • ad H)) Y := by
  rw [exp_ad_apply,exp_ad_apply,exp_ad_apply]
  have hc := mexp_smul_cancel H (-a)
  simp only [neg_neg] at hc
  calc
    _=mexp (a • H)*X*(mexp ((-a) • H)*mexp (a • H))*Y*mexp ((-a) • H) := by
      rw [hc,mul_one]
      noncomm_ring
    _=_ := by noncomm_ring

lemma ad_evolution_inverse (H X : Mat ι) (a : ℂ) :
    applySuper (mexp (a • ad H)) (applySuper (mexp ((-a) • ad H)) X)=X := by
  rw [← applySuper_mul,mexp_smul_cancel,applySuper_one]

lemma jump_orbit_expression {N : ℕ} (Q : Model N) (w : Disorder N) (β s : ℝ)
    (X : Mat (SiteHilbert N)) (i : Fin N) :
    applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w)))
      (applySuper (cMap Q w β i) (applySuper (mexp (((-s : ℂ)*Complex.I) • ad (hamiltonian Q w))) X))=
      (1/2 : ℂ) • (applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w))) (imaginary Q w (β/4) i)*X-
        X*applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w))) (imaginary Q w (-(β/4)) i)) := by
  let a : ℂ := (s : ℂ)*Complex.I
  have ha : ((-s : ℂ)*Complex.I)=-a := by dsimp only [a]; ring
  rw [ha,cMap_apply_commutator]
  change (act (mexp (a • ad (hamiltonian Q w)))) ((1/2 : ℂ) • _)=_
  rw [map_smul,map_sub]
  change (1/2 : ℂ) • (applySuper (mexp (a • ad (hamiltonian Q w)))
    (imaginary Q w (β/4) i*applySuper (mexp ((-a) • ad (hamiltonian Q w))) X)-
    applySuper (mexp (a • ad (hamiltonian Q w)))
      (applySuper (mexp ((-a) • ad (hamiltonian Q w))) X*imaginary Q w (-(β/4)) i))=_
  rw [ad_evolution_mul,ad_evolution_mul,ad_evolution_inverse]

lemma integrable_jump_orbit {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (X : Mat (SiteHilbert N)) (i : Fin N) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun s : ℝ ↦ applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w)))
      (applySuper (cMap Q w β i) (applySuper (mexp (((-s : ℂ)*Complex.I) • ad (hamiltonian Q w))) X))) μ := by
  simp_rw [jump_orbit_expression]
  have hA := integrable_ad_unitary (hamiltonian Q w) (hamiltonian_hermitian_words Q w) (imaginary Q w (β/4) i) μ
  have hB := integrable_ad_unitary (hamiltonian Q w) (hamiltonian_hermitian_words Q w) (imaginary Q w (-(β/4)) i) μ
  exact (((rightAct X).integrable_comp hA).sub ((leftAct X).integrable_comp hB)).smul (1/2 : ℂ)

lemma gaussian_jump_average {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (X : Mat (SiteHilbert N)) (i : Fin N) :
    (∫ s : ℝ, applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w)))
      (applySuper (cMap Q w β i) (applySuper (mexp (((-s : ℂ)*Complex.I) • ad (hamiltonian Q w))) X))
      ∂gaussianReal 0 (Real.toNNReal (β^2/4)))=applySuper (cfMap Q w β i) X := by
  let μ := gaussianReal 0 (Real.toNNReal (β^2/4))
  simp_rw [jump_orbit_expression]
  have hA := integrable_ad_unitary (hamiltonian Q w) (hamiltonian_hermitian_words Q w) (imaginary Q w (β/4) i) μ
  have hB := integrable_ad_unitary (hamiltonian Q w) (hamiltonian_hermitian_words Q w) (imaginary Q w (-(β/4)) i) μ
  have hAX : Integrable (fun s : ℝ ↦ applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w)))
      (imaginary Q w (β/4) i)*X) μ := (rightAct X).integrable_comp hA
  have hXB : Integrable (fun s : ℝ ↦ X*applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w)))
      (imaginary Q w (-(β/4)) i)) μ := (leftAct X).integrable_comp hB
  rw [integral_smul]
  change (1/2 : ℂ) • (∫ s : ℝ, applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w)))
      (imaginary Q w (β/4) i)*X-X*applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w)))
      (imaginary Q w (-(β/4)) i) ∂μ)=_
  rw [integral_sub hAX hXB,
    integral_mul_const_of_integrable hA,integral_const_mul_of_integrable hB,
    gaussian_imaginary_filter,gaussian_imaginary_filter]
  change _=applySuper (jumpDifference (jump (hamiltonian Q w) Q.γ β i)) X
  rw [jumpDifference_apply,jump_adjoint (hamiltonian Q w) (hamiltonian_hermitian_words Q w) Q.γ Q.car.herm β i]
  simp only [neg_neg,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat,jump]

def matrixEntryCLM (a b : ι) : Mat ι →L[ℂ] ℂ where
  toFun X := X a b
  map_add' X Y := rfl
  map_smul' z X := rfl
  cont := by fun_prop

lemma integrable_familyVec {μ : Measure Ω} (F : Ω → I → Mat ι)
    (hF : ∀ i, Integrable (fun t ↦ F t i) μ) : Integrable (fun t ↦ familyVec (F t)) μ := by
  apply Integrable.of_eval_piLp
  intro p
  exact (matrixEntryCLM p.2.1 p.2.2).integrable_comp (hF p.1)

lemma integral_familyVec {μ : Measure Ω} (F : Ω → I → Mat ι)
    (hF : ∀ i, Integrable (fun t ↦ F t i) μ) :
    (∫ t, familyVec (F t) ∂μ)=familyVec (fun i ↦ ∫ t, F t i ∂μ) := by
  apply PiLp.ext
  intro p
  rw [eval_integral_piLp (fun q ↦ (matrixEntryCLM q.2.1 q.2.2).integrable_comp (hF q.1)) p]
  change (∫ t, F t p.1 p.2.1 p.2.2 ∂μ)=(∫ t, F t p.1 ∂μ) p.2.1 p.2.2
  exact (matrixEntryCLM p.2.1 p.2.2).integral_comp_comm (hF p.1)


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

lemma integral_Ioi_translate (f : ℝ → ℝ) (a c : ℝ) :
    (∫ x in Ioi c, f (x-a))=∫ x in Ioi (c-a), f x := by
  have he : MeasurableEmbedding (fun x : ℝ ↦ x-a) := by
    simpa only [sub_eq_add_neg] using! (Homeomorph.addRight (-a)).measurableEmbedding
  have hm : Measure.map (fun x : ℝ ↦ x-a) volume=volume := by
    simpa only [sub_eq_add_neg] using Measure.IsAddRightInvariant.map_add_right_eq_self (μ := (volume : Measure ℝ)) (-a)
  have hh := he.setIntegral_map (μ := volume) f (Ioi (c-a))
  have hp : (fun x : ℝ ↦ x-a) ⁻¹' Ioi (c-a)=Ioi c := by ext x; simp
  rw [hm,hp] at hh
  exact hh.symm

lemma integrable_tilted_halfGaussian (a : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (-x^2/2+a*x)) := by
  have hg : Integrable (fun x : ℝ ↦ Real.exp (-x^2/2)) := by
    convert! integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num) using 1
    funext x
    congr 1
    ring
  have hh := (hg.comp_sub_right a).const_mul (Real.exp (a^2/2))
  convert! hh using 1
  funext x
  rw [← Real.exp_add]
  congr 1
  ring

lemma halfGaussian_shift_bound (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in Ioi 0, Real.exp (-x^2/2+a*x)) ≤
      Real.exp (a^2/2)*(Real.sqrt (2*Real.pi)/2+a) := by
  let g := fun x : ℝ ↦ Real.exp (-x^2/2)
  have hg : Integrable g := by
    convert! integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num) using 1
    funext x
    dsimp only [g]
    congr 1
    ring
  have hi : (∫ x in Ioi 0, Real.exp (-x^2/2+a*x))=
      Real.exp (a^2/2)*(∫ x in Ioi (-a), g x) := by
    have he (x : ℝ) : Real.exp (-x^2/2+a*x)=Real.exp (a^2/2)*g (x-a) := by
      dsimp only [g]
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [he]
    rw [integral_const_mul,integral_Ioi_translate,zero_sub]
  have hbase : (∫ x in Ioi 0, g x)=Real.sqrt (2*Real.pi)/2 := by
    convert! integral_gaussian_Ioi (1/2 : ℝ) using 1
    · congr 1
      funext x
      dsimp only [g]
      congr 1
      ring
    · congr 2
      ring
  have hcut : (∫ x in -a..0, g x) ≤ a := by
    have he := intervalIntegral.integral_mono_on (a := -a) (b := 0) (f := g) (g := fun _ ↦ (1 : ℝ))
      (by linarith) hg.intervalIntegrable intervalIntegrable_const
      (fun x hx ↦ Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))
    simpa only [intervalIntegral.integral_const,sub_neg_eq_add,zero_add,smul_eq_mul,mul_one] using he
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (a := -a) (b := 0) hg.integrableOn hg.integrableOn
  rw [hi]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [← hsplit,hbase]
  linarith

lemma standardGaussian_filter_error_bound (a : ℝ) (ha : 0 ≤ a) :
    (∫ x : ℝ, (Real.exp (a*|x|)-1) ∂gaussianReal 0 1) ≤
      Real.exp (a^2/2)*(1+(5/6 : ℝ)*a)-1 := by
  let c := (Real.sqrt (2*Real.pi))⁻¹
  let g := fun x : ℝ ↦ Real.exp (-x^2/2)
  have hroot : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hcg : c*Real.sqrt (2*Real.pi)=1 := inv_mul_cancel₀ hroot.ne'
  have hc : 0 ≤ c := inv_nonneg.mpr hroot.le
  have hcoef : 2*c ≤ (5/6 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
    have hp := Real.pi_gt_three
    have hl : (12/5 : ℝ) ≤ Real.sqrt (2*Real.pi) := by nlinarith
    dsimp only [c]
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hroot).mpr
    nlinarith
  have hg : Integrable g := by
    convert! integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num) using 1
    funext x
    dsimp only [g]
    congr 1
    ring
  have hbase : (∫ x in Ioi 0, g x)=Real.sqrt (2*Real.pi)/2 := by
    convert! integral_gaussian_Ioi (1/2 : ℝ) using 1
    · congr 1; funext x; dsimp only [g]; congr 1; ring
    · congr 2; ring
  have hform : (∫ x : ℝ, (Real.exp (a*|x|)-1) ∂gaussianReal 0 1)=
      2*c*((∫ x in Ioi 0, Real.exp (-x^2/2+a*x))-Real.sqrt (2*Real.pi)/2) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0)≠0)]
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,smul_eq_mul,mul_assoc]
    rw [integral_const_mul]
    have he : (fun x : ℝ ↦ Real.exp (-x^2/2)*(Real.exp (a*|x|)-1))=
        (fun x : ℝ ↦ g |x| *(Real.exp (a*|x|)-1)) := by funext x; simp [g,sq_abs]
    rw [he,integral_comp_abs (f := fun r : ℝ ↦ g r*(Real.exp (a*r)-1))]
    have hx (x : ℝ) : g x*(Real.exp (a*x)-1)=Real.exp (-x^2/2+a*x)-g x := by
      dsimp only [g]
      rw [mul_sub,mul_one,← Real.exp_add]
    simp_rw [hx]
    rw [integral_sub (integrable_tilted_halfGaussian a).integrableOn hg.integrableOn,hbase]
    dsimp only [c]
    ring
  rw [hform]
  have ht := halfGaussian_shift_bound a ha
  have he := Real.exp_pos (a^2/2)
  have hm : 2*c*a ≤ (5/6 : ℝ)*a := mul_le_mul_of_nonneg_right hcoef ha
  calc
    _ ≤ 2*c*(Real.exp (a^2/2)*(Real.sqrt (2*Real.pi)/2+a)-Real.sqrt (2*Real.pi)/2) := by
      gcongr
    _ = Real.exp (a^2/2)*(1+2*c*a)-1 := by
      calc
        _=Real.exp (a^2/2)*(c*Real.sqrt (2*Real.pi)+2*c*a)-c*Real.sqrt (2*Real.pi) := by ring
        _=_ := by rw [hcg]
    _ ≤ _ := by gcongr

lemma standardGaussian_filter_error_small :
    (∫ x : ℝ, (Real.exp ((3/40 : ℝ)*|x|)-1) ∂gaussianReal 0 1) ≤ (1/14 : ℝ) := by
  have he := standardGaussian_filter_error_bound (3/40) (by norm_num)
  have hx := Real.exp_bound_div_one_sub_of_interval (x := (3/40 : ℝ)^2/2) (by norm_num) (by norm_num)
  norm_num at hx he ⊢
  nlinarith

lemma integrable_gaussian_filter_error (m : ℝ) (v : ℝ≥0) :
    Integrable (fun s : ℝ ↦ Real.exp (m*|s|)-1) (gaussianReal 0 v) := by
  exact (integrable_exp_mul_abs (integrable_exp_mul_gaussianReal m)
    (integrable_exp_mul_gaussianReal (-m))).sub (integrable_const 1)

lemma gaussian_filter_error_scaled (β m : ℝ) (hβ : 0 ≤ β) (hbm : m*β ≤ (3/20 : ℝ)) :
    (∫ s : ℝ, (Real.exp (m*|s|)-1) ∂gaussianReal 0 (Real.toNNReal (β^2/4))) ≤ (1/14 : ℝ) := by
  have hv : NNReal.mk ((β/2)^2) (sq_nonneg (β/2))=Real.toNNReal (β^2/4) := by
    apply NNReal.eq
    change (β/2)^2=((Real.toNNReal (β^2/4)) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity)]
    ring
  have hmap : (gaussianReal 0 1).map (fun x : ℝ ↦ (β/2)*x)=gaussianReal 0 (Real.toNNReal (β^2/4)) := by
    have he := gaussianReal_map_const_mul (μ := 0) (v := 1) (β/2)
    simp only [mul_zero,mul_one] at he
    rw [hv] at he
    exact he
  rw [← hmap,integral_map (by fun_prop) (by fun_prop)]
  have habs (x : ℝ) : m*|(β/2)*x|=(m*β/2)*|x| := by
    rw [abs_mul,abs_of_nonneg (div_nonneg hβ (by norm_num))]
    ring
  simp_rw [habs]
  have hi1 := integrable_gaussian_filter_error (m*β/2) 1
  have hi2 := integrable_gaussian_filter_error (3/40) 1
  apply le_trans (integral_mono hi1 hi2 ?_) standardGaussian_filter_error_small
  intro x
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg x)
  linarith


end SYKFastMix.FastMixing
end

section
namespace SYKFastMix.FastMixing

end SYKFastMix.FastMixing
open SYKFastMix.FastMixing
theorem solution {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (hβ : 0 ≤ β*Q.J ∧ β*Q.J ≤ 1/1000)
    (hM : SYKEdge.opNorm (blockM Q w (β/4)) ≤ 150*Q.J) :
    ∀ X, Real.sqrt (∑ i, hsSq (applySuper (cfMap Q w β i) X-applySuper (cMap Q w β i) X)) ≤
      (1/14 : ℝ)*Real.sqrt (∑ i, hsSq (applySuper (cMap Q w β i) X)) := by
  intro X
  have hβ0 : 0 ≤ β := by nlinarith [Q.positive,hβ.1]
  let μ := gaussianReal 0 (Real.toNNReal (β^2/4))
  let V := fun s : ℝ ↦ familyVec (fun i ↦
    applySuper (mexp (((s : ℂ)*Complex.I) • ad (hamiltonian Q w)))
      (applySuper (cMap Q w β i) (applySuper (mexp (((-s : ℂ)*Complex.I) • ad (hamiltonian Q w))) X)))
  let C := familyVec (fun i ↦ applySuper (cMap Q w β i) X)
  let F := familyVec (fun i ↦ applySuper (cfMap Q w β i) X)
  have hiV : Integrable V μ := integrable_familyVec _ (fun i ↦ integrable_jump_orbit Q w β X i μ)
  have hVC : Integrable (fun s ↦ V s-C) μ := hiV.sub (integrable_const C)
  have hAvg : (∫ s, V s ∂μ)=F := by
    dsimp only [V,F,μ]
    rw [integral_familyVec _ (fun i ↦ integrable_jump_orbit Q w β X i _)]
    simp_rw [gaussian_jump_average]
  have hDiff : (∫ s, (V s-C) ∂μ)=F-C := by
    rw [integral_sub hiV (integrable_const C),hAvg]
    simp [μ]
  have hbound (s : ℝ) : ‖V s-C‖ ≤ (Real.exp ((150*Q.J)*|s|)-1)*‖C‖ :=
    jump_tuple_displacement Q w β hβ0 hM X s
  have hiScalar := integrable_gaussian_filter_error (150*Q.J) (Real.toNNReal (β^2/4))
  have hScalar : (∫ s : ℝ, (Real.exp ((150*Q.J)*|s|)-1) ∂μ) ≤ (1/14 : ℝ) := by
    apply gaussian_filter_error_scaled β (150*Q.J) hβ0
    nlinarith [hβ.2]
  have hfinal : ‖F-C‖ ≤ (1/14 : ℝ)*‖C‖ := by
    calc
      _ = ‖∫ s, (V s-C) ∂μ‖ := by rw [hDiff]
      _ ≤ ∫ s, ‖V s-C‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ s, (Real.exp ((150*Q.J)*|s|)-1)*‖C‖ ∂μ :=
        integral_mono hVC.norm (hiScalar.mul_const ‖C‖) hbound
      _ = (∫ s, (Real.exp ((150*Q.J)*|s|)-1) ∂μ)*‖C‖ := integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hScalar (norm_nonneg C)
  rw [← familyVec_norm,← familyVec_norm,familyVec_sub]
  exact hfinal


namespace SYKFastMix.FastMixing

end SYKFastMix.FastMixing
end
