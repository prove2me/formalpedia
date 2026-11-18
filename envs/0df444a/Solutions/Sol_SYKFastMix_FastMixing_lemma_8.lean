-- Prove2me | solution 1 for SYKFastMix.FastMixing.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:12:28.116628+00:00
-- url     : https://prove2.me/submissions/0e268910-3d44-4f50-8539-2fe832b9a963

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Operators
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_Model
import Theorems.Thm_SYKFastMix_FastMixing_lemma_7

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator
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


noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace SYKFastMix.FastMixing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma hermitian_norm_eq_eigenvalues_norm (B : Mat ι) (hB : B.IsHermitian) :
    ‖B‖ = ‖fun i ↦ (hB.eigenvalues i : ℂ)‖ := by
  conv_lhs => rw [hB.spectral_theorem]
  rw [StarAlgEquiv.norm_map, Matrix.l2_opNorm_diagonal]
  rfl

lemma traceMoment_eq_sum_eigenvalues_pow (p : ℕ) (A : Mat ι) :
    traceMoment p A = ∑ i, ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) ^ p := by
  let hB := Matrix.isHermitian_conjTranspose_mul_self A
  unfold traceMoment
  conv_lhs => rw [hB.spectral_theorem, ← map_pow]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Pi.pow_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change (((hB.eigenvalues i : ℝ) : ℂ) ^ p).re = _
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma traceMoment_nonneg (p : ℕ) (A : Mat ι) : 0 ≤ traceMoment p A := by
  rw [traceMoment_eq_sum_eigenvalues_pow]
  exact Finset.sum_nonneg fun i _ ↦ pow_nonneg (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i) _

lemma opNorm_pow_le_traceMoment [Nonempty ι] (p : ℕ) (A : Mat ι) :
    SYKEdge.opNorm A ^ (2*p) ≤ traceMoment p A := by
  let hB := Matrix.isHermitian_conjTranspose_mul_self A
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ hB.eigenvalues Finset.univ_nonempty
  have hn (j : ι) : 0 ≤ hB.eigenvalues j := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A j
  have he : ‖Aᴴ * A‖ = hB.eigenvalues i := by
    rw [hermitian_norm_eq_eigenvalues_norm _ hB]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (hn i)).mpr
      intro j
      change ‖(hB.eigenvalues j : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_of_nonneg (hn j)]
      exact hmax j (Finset.mem_univ j)
    · have h := norm_le_pi_norm (fun j ↦ (hB.eigenvalues j : ℂ)) i
      simpa only [Complex.norm_real, Real.norm_of_nonneg (hn i)] using h
  rw [traceMoment_eq_sum_eigenvalues_pow]
  calc
    SYKEdge.opNorm A ^ (2*p) = ‖Aᴴ * A‖ ^ p := by
      change ‖A‖ ^ (2*p) = _
      rw [Matrix.l2_opNorm_conjTranspose_mul_self, ← pow_two, pow_mul]
    _ = hB.eigenvalues i ^ p := by rw [he]
    _ ≤ ∑ j, hB.eigenvalues j ^ p :=
      Finset.single_le_sum (fun j _ ↦ pow_nonneg (hn j) p) (Finset.mem_univ i)

lemma traceMoment_le_card_mul_opNorm_pow (p : ℕ) (A : Mat ι) :
    traceMoment p A ≤ (Fintype.card ι : ℝ) * SYKEdge.opNorm A ^ (2*p) := by
  let hB := Matrix.isHermitian_conjTranspose_mul_self A
  have hn (j : ι) : 0 ≤ hB.eigenvalues j := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A j
  have he (j : ι) : hB.eigenvalues j ≤ ‖Aᴴ * A‖ := by
    rw [hermitian_norm_eq_eigenvalues_norm _ hB]
    have h := norm_le_pi_norm (fun j ↦ (hB.eigenvalues j : ℂ)) j
    simpa only [Complex.norm_real, Real.norm_of_nonneg (hn j)] using h
  rw [traceMoment_eq_sum_eigenvalues_pow]
  calc
    ∑ j, hB.eigenvalues j ^ p ≤ ∑ _ : ι, ‖Aᴴ * A‖ ^ p :=
      Finset.sum_le_sum (fun j _ ↦ pow_le_pow_left₀ (hn j) (he j) p)
    _ = (Fintype.card ι : ℝ) * SYKEdge.opNorm A ^ (2*p) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      change ‖Aᴴ * A‖ ^ p = ‖A‖ ^ (2*p)
      rw [Matrix.l2_opNorm_conjTranspose_mul_self, ← pow_two, pow_mul]

end SYKFastMix.FastMixing



noncomputable section
open scoped Matrix.Norms.L2Operator
open scoped ComplexConjugate
open Matrix
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


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma hsSq_eq_traceMoment_one (X : Mat ι) : hsSq X = traceMoment 1 X := by
  simp [hsSq, hsInner, traceMoment]

lemma traceNorm_nonneg (X : Mat ι) : 0 ≤ traceNorm X := by
  unfold traceNorm
  positivity

lemma traceNorm_le_sqrt_card_mul_hs (X : Mat ι) :
    traceNorm X ≤ Real.sqrt (Fintype.card ι : ℝ) * hs X := by
  let ev := (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues
  have hev (i : ι) : 0 ≤ ev i := Matrix.eigenvalues_conjTranspose_mul_self_nonneg X i
  have hsum : hsSq X = ∑ i, ev i := by
    rw [hsSq_eq_traceMoment_one, traceMoment_eq_sum_eigenvalues_pow]
    simp [ev]
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : ι ↦ Real.sqrt (ev i))
  simp only [Finset.card_univ, Real.sq_sqrt (hev _)] at h
  have he : (Real.sqrt (Fintype.card ι : ℝ) * hs X)^2 = (Fintype.card ι : ℝ) * hsSq X := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hs, Real.sq_sqrt (hsSq_nonneg X)]
  apply (sq_le_sq₀ (traceNorm_nonneg X) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  change (traceNorm X)^2 ≤ (Real.sqrt (Fintype.card ι : ℝ) * hs X)^2
  rw [he, hsum]
  exact h

lemma hsSq_hermitian_eq_sum_eigenvalues_sq (X : Mat ι) (hX : X.IsHermitian) :
    hsSq X = ∑ i, (hX.eigenvalues i)^2 := by
  unfold hsSq hsInner
  rw [hX.eq]
  conv_lhs => rw [hX.spectral_theorem, ← map_mul]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Function.comp_apply, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change ((hX.eigenvalues i : ℂ) * (hX.eigenvalues i : ℂ)).re = _
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  ring

lemma density_hsSq_le_one (X : Mat ι) (hX : IsDensity X) : hsSq X ≤ 1 := by
  have hpos := hX.1
  have hherm := hpos.isHermitian
  have hsum : (∑ i, hherm.eigenvalues i) = (1 : ℝ) := by
    have h := hherm.trace_eq_sum_eigenvalues
    rw [hX.2] at h
    have hre := congrArg Complex.re h
    simpa using hre.symm
  rw [hsSq_hermitian_eq_sum_eigenvalues_sq X hherm]
  calc
    _ ≤ (∑ i, hherm.eigenvalues i)^2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i hi ↦ hpos.eigenvalues_nonneg i)
    _ = 1 := by rw [hsum]; norm_num

lemma hsSq_eq_sum_columns (X : Mat ι) : hsSq X = ∑ j, ∑ i, ‖X i j‖^2 := by
  rw [hsSq_eq_sum_norm_sq]
  simp only [opVec, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

lemma hsSq_mul_left_le (A X : Mat ι) : hsSq (A*X) ≤ ‖A‖^2 * hsSq X := by
  have hcol (j : ι) : (∑ i, ‖(A*X) i j‖^2) ≤ ‖A‖^2 * ∑ i, ‖X i j‖^2 := by
    let x : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i ↦ X i j)
    have h := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm x
    have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [mul_pow] at h'
    change ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x‖^2 ≤ ‖A‖^2 * ‖x‖^2 at h'
    convert! h' using 1
    · simp only [EuclideanSpace.norm_sq_eq, x, Matrix.toEuclideanCLM_toLp,
        WithLp.ofLp_toLp, Matrix.mulVec, Matrix.mul_apply, dotProduct]
    · simp only [EuclideanSpace.norm_sq_eq, x, WithLp.ofLp_toLp]
  rw [hsSq_eq_sum_columns, hsSq_eq_sum_columns, Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj ↦ hcol j

lemma hsSq_conjTranspose (X : Mat ι) : hsSq Xᴴ = hsSq X := by
  rw [hsSq_eq_sum_columns, hsSq_eq_sum_columns]
  simp only [Matrix.conjTranspose_apply, norm_star]
  rw [Finset.sum_comm]

lemma hsSq_mul_right_le (X A : Mat ι) : hsSq (X*A) ≤ ‖A‖^2 * hsSq X := by
  have h := hsSq_mul_left_le Aᴴ Xᴴ
  simpa only [← Matrix.conjTranspose_mul, hsSq_conjTranspose, Matrix.l2_opNorm_conjTranspose] using h

lemma hs_mul_left_le (A X : Mat ι) : hs (A*X) ≤ ‖A‖ * hs X := by
  have h := hsSq_mul_left_le A X
  have he (Y : Mat ι) : (hs Y)^2 = hsSq Y := Real.sq_sqrt (hsSq_nonneg Y)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
  change (hs (A*X))^2 ≤ (‖A‖ * hs X)^2
  rw [mul_pow, he, he]
  exact h

lemma hs_mul_right_le (X A : Mat ι) : hs (X*A) ≤ hs X * ‖A‖ := by
  have h := hs_mul_left_le Aᴴ Xᴴ
  have he (Y : Mat ι) : hs Yᴴ = hs Y := by rw [hs, hsSq_conjTranspose]; rfl
  simpa only [← Matrix.conjTranspose_mul, he, Matrix.l2_opNorm_conjTranspose, mul_comm] using h

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

lemma hs_projection_bound (R W : Mat ι) (Z : ℝ) (hZ : 0 < Z)
    (hRR : hsSq R = Z) (hRW : hsInner R W = 1) :
    hsInner R (W - (Z⁻¹ : ℂ) • R) = 0 ∧ hsSq (W - (Z⁻¹ : ℂ) • R) ≤ hsSq W := by
  have hR : hsInner R R = (Z : ℂ) := by rw [hsInner_self_real, hRR]
  have hWR : hsInner W R = 1 := by rw [hsInner_conj_symm, hRW]; simp
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  constructor
  · rw [hsInner_sub_right, hsInner_smul_right, hRW, hR]
    simp [hZc]
  · have he : hsInner (W - (Z⁻¹ : ℂ) • R) (W - (Z⁻¹ : ℂ) • R) =
        hsInner W W - (Z⁻¹ : ℂ) := by
      simp only [hsInner_sub_left, hsInner_sub_right, hsInner_smul_left, hsInner_smul_right,
        hRW, hWR, hR, Complex.conj_ofReal, Complex.ofReal_inv]
      field_simp
      <;> ring
    unfold hsSq
    rw [he, Complex.sub_re, ← Complex.ofReal_inv, Complex.ofReal_re]
    exact sub_le_self _ (inv_nonneg.mpr hZ.le)

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
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

lemma mexp_norm_le [Nonempty ι] (H : Mat ι) : ‖mexp H‖ ≤ Real.exp ‖H‖ := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) H
  have hr := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖H‖
  rw [← Real.exp_eq_exp_ℝ] at hr
  apply h.norm_le_of_bounded hr
  intro n
  simp only [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le H n) (by positivity)

lemma mexp_smul_norm_le [Nonempty ι] (H : Mat ι) (a : ℝ) :
    ‖mexp ((a : ℂ) • H)‖ ≤ Real.exp (|a| * ‖H‖) := by
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs] using mexp_norm_le ((a : ℂ) • H)

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

lemma weighted_density_inner (H : Mat ι) (hH : H.IsHermitian) (β : ℝ) (X : Mat ι) :
    hsInner (mexp (((-(β/2) : ℝ) : ℂ) • H))
      (mexp (((β/4 : ℝ) : ℂ) • H) * X * mexp (((β/4 : ℝ) : ℂ) • H)) = Matrix.trace X := by
  let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
  let B := mexp (((β/4 : ℝ) : ℂ) • H)
  have hBRB : B*R*B=1 := by
    change mexp (((β/4 : ℝ) : ℂ) • H) * mexp (((-(β/2) : ℝ) : ℂ) • H) *
      mexp (((β/4 : ℝ) : ℂ) • H) = 1
    rw [mexp_smul_add, mexp_smul_add]
    have hz : (((β/4 : ℝ) : ℂ) + ((-(β/2) : ℝ) : ℂ) + ((β/4 : ℝ) : ℂ)) = 0 := by
      push_cast
      ring
    rw [hz]
    simp [mexp]
  change Matrix.trace (Rᴴ * (B*X*B)) = _
  rw [(mexp_hermitian H hH (-(β/2))).eq]
  calc
    Matrix.trace (R * (B*X*B)) = Matrix.trace ((R*B)*X*B) := by congr 1; noncomm_ring
    _ = Matrix.trace (B*(R*B)*X) := Matrix.trace_mul_cycle (R*B) X B
    _ = Matrix.trace ((B*R*B)*X) := by congr 1; noncomm_ring
    _ = _ := by rw [hBRB, one_mul]

lemma weighted_density_hs_le [Nonempty ι] (H : Mat ι) (β : ℝ) (hβ : 0 ≤ β)
    (X : Mat ι) (hX : IsDensity X) :
    hs (mexp (((β/4 : ℝ) : ℂ) • H) * X * mexp (((β/4 : ℝ) : ℂ) • H)) ≤
      Real.exp (β * ‖H‖ / 2) := by
  let B := mexp (((β/4 : ℝ) : ℂ) • H)
  have hB : ‖B‖ ≤ Real.exp (β/4 * ‖H‖) := by
    simpa only [abs_of_nonneg (by positivity : 0 ≤ β/4)] using mexp_smul_norm_le H (β/4)
  have hnorm : hs X ≤ 1 := by
    have h := density_hsSq_le_one X hX
    have hsqr := Real.sq_sqrt (hsSq_nonneg X)
    change Real.sqrt (hsSq X) ≤ 1
    nlinarith [Real.sqrt_nonneg (hsSq X)]
  calc
    _ = hs (B*(X*B)) := by rw [mul_assoc]
    _ ≤ ‖B‖ * hs (X*B) := hs_mul_left_le B (X*B)
    _ ≤ Real.exp (β/4*‖H‖) * (1 * Real.exp (β/4*‖H‖)) := by
      apply mul_le_mul hB ?_ (Real.sqrt_nonneg _) (Real.exp_pos _).le
      exact (hs_mul_right_le X B).trans (mul_le_mul hnorm hB (norm_nonneg _) (by norm_num))
    _ = _ := by rw [one_mul, ← Real.exp_add]; congr 1 <;> ring

lemma weighted_density_projection [Nonempty ι] (H : Mat ι) (hH : H.IsHermitian)
    (β : ℝ) (hβ : 0 ≤ β) (X : Mat ι) (hX : IsDensity X) :
    let Z := (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re
    let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
    let W := mexp (((β/4 : ℝ) : ℂ) • H) * X * mexp (((β/4 : ℝ) : ℂ) • H)
    hsInner (gibbsRoot H β) (W - (Z⁻¹ : ℂ) • R) = 0 ∧
      hs (W - (Z⁻¹ : ℂ) • R) ≤ Real.exp (β * ‖H‖ / 2) := by
  dsimp only
  have hZ := mexp_trace_pos H hH (-β)
  have hp := hs_projection_bound (mexp (((-(β/2) : ℝ) : ℂ) • H))
    (mexp (((β/4 : ℝ) : ℂ) • H) * X * mexp (((β/4 : ℝ) : ℂ) • H))
    ((Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re) hZ (mexp_half_hsSq H hH β)
    (by rw [weighted_density_inner H hH β X, hX.2])
  constructor
  · unfold gibbsRoot
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat] at hp ⊢
    rw [hsInner_smul_left, hp.1, mul_zero]
  · apply le_trans (Real.sqrt_le_sqrt hp.2)
    exact weighted_density_hs_le H β hβ X hX

lemma gibbs_congruence_identity (H : Mat ι) (hH : H.IsHermitian) (β : ℝ) :
    let Z := (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re
    let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
    let C := mexp (((-(β/4) : ℝ) : ℂ) • H)
    C * ((Z⁻¹ : ℂ) • R) * C = gibbs H β := by
  dsimp only
  rw [mul_smul_comm, smul_mul_assoc]
  have he : mexp (((-(β/4) : ℝ) : ℂ) • H) * mexp (((-(β/2) : ℝ) : ℂ) • H) *
      mexp (((-(β/4) : ℝ) : ℂ) • H) = mexp (((-β : ℝ) : ℂ) • H) := by
    rw [mexp_smul_add, mexp_smul_add]
    congr 1
    congr 1
    push_cast
    ring
  rw [he]
  have hz : Matrix.trace (mexp (((-β : ℝ) : ℂ) • H)) =
      ((Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re : ℂ) := by
    rw [mexp_trace H hH (-β)]
    simp only [Complex.ofReal_re]
  unfold gibbs
  simp only [Complex.ofReal_neg] at hz ⊢
  rw [hz]
  simp only [Complex.ofReal_re]

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma gamma_mul_word {N : ℕ} (Q : Model N) (j : Fin N) (l : List (Fin N)) :
    Q.γ j * (l.map Q.γ).prod =
      (-1 : ℂ)^((l.filter (· != j)).length) • ((l.map Q.γ).prod * Q.γ j) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    let c : ℂ := if i=j then 1 else -1
    have hs : Q.γ j * Q.γ i = c • (Q.γ i * Q.γ j) := by
      by_cases hij : i=j
      · simp [c, hij]
      · simpa [c, hij] using Q.car.anticomm j i (Ne.symm hij)
    have hcount : (-1 : ℂ)^(((i::l).filter (· != j)).length) = c * (-1 : ℂ)^((l.filter (· != j)).length) := by
      by_cases hij : i=j <;> simp [c, hij, pow_succ, mul_comm]
    simp only [List.map_cons, List.prod_cons]
    calc
      Q.γ j * (Q.γ i * (l.map Q.γ).prod) = (Q.γ j * Q.γ i) * (l.map Q.γ).prod := by rw [mul_assoc]
      _ = c • (Q.γ i * (Q.γ j * (l.map Q.γ).prod)) := by rw [hs, smul_mul_assoc, mul_assoc]
      _ = c • (Q.γ i * ((-1 : ℂ)^((l.filter (· != j)).length) • ((l.map Q.γ).prod * Q.γ j))) := by rw [ih]
      _ = (-1 : ℂ)^(((i::l).filter (· != j)).length) • ((Q.γ i * (l.map Q.γ).prod) * Q.γ j) := by
        rw [mul_smul_comm, smul_smul, ← hcount, mul_assoc]

lemma rawString_character {N : ℕ} (Q : Model N) (S : Finset (Fin N)) (j : Fin N) :
    Q.γ j * rawString Q S * Q.γ j = (-1 : ℂ)^((S.erase j).card) • rawString Q S := by
  have hlen : ((S.sort (· ≤ ·)).filter (· != j)).length = (S.erase j).card := by
    have hn := (S.sort_nodup (· ≤ ·)).filter (· != j)
    have he : ((S.sort (· ≤ ·)).filter (· != j)).toFinset = S.erase j := by
      ext k
      simp [and_comm]
    rw [← he]
    exact (List.toFinset_card_of_nodup hn).symm
  unfold rawString
  rw [gamma_mul_word, smul_mul_assoc, mul_assoc, Q.car.sq, mul_one, hlen]

lemma rawString_unitary_word {N : ℕ} (Q : Model N) (S : Finset (Fin N)) :
    rawString Q S ∈ unitary (Mat (SiteHilbert N)) := by
  unfold rawString
  apply Submonoid.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  apply Unitary.mem_iff.mpr
  change (Q.γ i)ᴴ * Q.γ i = 1 ∧ Q.γ i * (Q.γ i)ᴴ = 1
  rw [(Q.car.herm i).eq]
  exact ⟨Q.car.sq i, Q.car.sq i⟩

def hsInnerLinear {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) : Mat ι →ₗ[ℂ] ℂ where
  toFun := hsInner X
  map_add' Y Z := by simp [hsInner, mul_add]
  map_smul' z Y := by rw [hsInner_smul_right]; rfl

lemma word_conjTranspose {N : ℕ} (Q : Model N) (l : List (Fin N)) (hl : l.Nodup) :
    ((l.map Q.γ).prod)ᴴ = (-1 : ℂ)^(l.length.choose 2) • (l.map Q.γ).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hin : i ∉ l := (List.nodup_cons.mp hl).1
    have hnodup : l.Nodup := (List.nodup_cons.mp hl).2
    have hfilter : l.filter (· != i)=l := by
      apply List.filter_eq_self.mpr
      intro j hj
      simp only [bne_iff_ne]
      exact fun h ↦ hin (h ▸ hj)
    have hm := gamma_mul_word Q i l
    rw [hfilter] at hm
    have hs : (-1 : ℂ)^l.length * (-1 : ℂ)^l.length=1 := by
      rcases neg_one_pow_eq_or ℂ l.length with h | h <;> simp [h]
    have hmove : (l.map Q.γ).prod * Q.γ i = (-1 : ℂ)^l.length • (Q.γ i * (l.map Q.γ).prod) := by
      rw [hm, smul_smul, hs, one_smul]
    simp only [List.map_cons, List.prod_cons, Matrix.conjTranspose_mul, (Q.car.herm i).eq,
      List.length_cons]
    rw [ih hnodup, smul_mul_assoc, hmove, smul_smul, ← pow_add]
    congr 1
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

lemma rawString_conjTranspose {N : ℕ} (Q : Model N) (S : Finset (Fin N)) :
    (rawString Q S)ᴴ = (-1 : ℂ)^(S.card.choose 2) • rawString Q S := by
  have h := word_conjTranspose Q (S.sort (· ≤ ·)) (S.sort_nodup (· ≤ ·))
  simpa [rawString] using h

lemma rawString_mul_self {N : ℕ} (Q : Model N) (S : Finset (Fin N)) :
    rawString Q S * rawString Q S = (-1 : ℂ)^(S.card.choose 2) • (1 : Mat (SiteHilbert N)) := by
  have h := Unitary.star_mul_self_of_mem (rawString_unitary_word Q S)
  change (rawString Q S)ᴴ * rawString Q S=1 at h
  have hs : (-1 : ℂ)^(S.card.choose 2) * (-1 : ℂ)^(S.card.choose 2)=1 := by
    rcases neg_one_pow_eq_or ℂ (S.card.choose 2) with h | h <;> simp [h]
  have he := congrArg (fun A : Mat (SiteHilbert N) ↦ (-1 : ℂ)^(S.card.choose 2) • A) h
  rwa [rawString_conjTranspose, smul_mul_assoc, smul_smul, hs, one_smul] at he

lemma half_add_choose_two_even {N : ℕ} (hN : Even N) : Even (N/2 + N.choose 2) := by
  rcases hN with ⟨k, rfl⟩
  have hhalf : (k+k)/2=k := by omega
  rw [hhalf, Nat.choose_two_right]
  have hc : (k+k)*(k+k-1)/2 = k*(k+k-1) := by
    rw [show (k+k)*(k+k-1)=k*(k+k-1)*2 by ring, Nat.mul_div_left]
    norm_num
  rw [hc]
  by_cases hk : k=0
  · simp [hk]
  · have hpos : 1 ≤ k+k := by omega
    have hsub := Nat.sub_add_cancel hpos
    refine ⟨k*k, ?_⟩
    nlinarith

lemma parityMatrix_sq {N : ℕ} (Q : Model N) : parityMatrix Q * parityMatrix Q=1 := by
  unfold parityMatrix
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, rawString_mul_self, smul_smul]
  simp only [Finset.card_univ, Fintype.card_fin]
  have hi : Complex.I^(N/2) * Complex.I^(N/2) = (-1 : ℂ)^(N/2) := by
    rw [← mul_pow, Complex.I_mul_I]
  rw [hi, ← pow_add, (half_add_choose_two_even Q.even).neg_one_pow, one_smul]

lemma parityMatrix_anticomm {N : ℕ} (Q : Model N) (i : Fin N) :
    Q.γ i * parityMatrix Q = -(parityMatrix Q * Q.γ i) := by
  have hodd : Odd (N-1) := by
    apply Nat.odd_iff.mpr
    have he := Nat.even_iff.mp Q.even
    have hs := Q.size
    omega
  have h := rawString_character Q Finset.univ i
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    hodd.neg_one_pow, neg_one_smul] at h
  have hm := congrArg (fun A : Mat (SiteHilbert N) ↦ A * Q.γ i) h
  have hr : Q.γ i * rawString Q Finset.univ = -(rawString Q Finset.univ * Q.γ i) := by
    simpa only [mul_assoc, Q.car.sq, mul_one, neg_mul] using hm
  unfold parityMatrix
  rw [mul_smul_comm, hr, smul_neg, smul_mul_assoc]

lemma parity_mul {N : ℕ} (Q : Model N) (X Y : Mat (SiteHilbert N)) :
    parity Q (X*Y)=parity Q X * parity Q Y := by
  unfold parity
  symm
  calc
    _ = (parityMatrix Q * X) * (parityMatrix Q * parityMatrix Q) * (Y * parityMatrix Q) := by noncomm_ring
    _ = _ := by rw [parityMatrix_sq]; noncomm_ring

lemma parity_involution {N : ℕ} (Q : Model N) (X : Mat (SiteHilbert N)) :
    parity Q (parity Q X)=X := by
  unfold parity
  calc
    _ = (parityMatrix Q * parityMatrix Q) * X * (parityMatrix Q * parityMatrix Q) := by noncomm_ring
    _ = _ := by rw [parityMatrix_sq, one_mul, mul_one]

lemma parity_gamma {N : ℕ} (Q : Model N) (i : Fin N) : parity Q (Q.γ i) = -Q.γ i := by
  unfold parity
  have h := parityMatrix_anticomm Q i
  calc
    _ = -(Q.γ i * parityMatrix Q) * parityMatrix Q := by rw [h, neg_neg]
    _ = _ := by rw [neg_mul, mul_assoc, parityMatrix_sq, mul_one]

lemma parityMatrix_hermitian {N : ℕ} (Q : Model N) : (parityMatrix Q).IsHermitian := by
  have hu := Unitary.star_mul_self_of_mem (rawString_unitary_word Q Finset.univ)
  change (rawString Q Finset.univ)ᴴ * rawString Q Finset.univ=1 at hu
  have hunit : (parityMatrix Q)ᴴ * parityMatrix Q=1 := by
    unfold parityMatrix
    rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hu]
    simp only [star_pow, ← mul_pow]
    have hi : star Complex.I * Complex.I=1 := by simp [Complex.conj_I, Complex.I_mul_I]
    rw [hi, one_pow, one_smul]
  have h := congrArg (fun A : Mat (SiteHilbert N) ↦ A * parityMatrix Q) hunit
  rw [mul_assoc, parityMatrix_sq, mul_one, one_mul] at h
  exact h

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma parity_word {N : ℕ} (Q : Model N) (l : List (Fin N)) :
    parity Q (l.map Q.γ).prod = (-1 : ℂ)^l.length • (l.map Q.γ).prod := by
  induction l with
  | nil => simp [parity, parityMatrix_sq]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [parity_mul, parity_gamma, ih, mul_smul_comm, pow_succ]
    simp only [mul_neg_one, neg_smul, neg_mul, smul_neg]

lemma parity_rawString {N : ℕ} (Q : Model N) (S : Finset (Fin N)) :
    parity Q (rawString Q S)=(-1 : ℂ)^S.card • rawString Q S := by
  simpa only [rawString, Finset.length_sort] using parity_word Q (S.sort (· ≤ ·))

lemma hamiltonian_hermitian_words {N : ℕ} (Q : Model N) (w : Disorder N) :
    (hamiltonian Q w).IsHermitian := by
  unfold hamiltonian Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Matrix.conjTranspose_smul, rawString_conjTranspose]
  norm_num [A.2, Nat.choose]

lemma parity_hamiltonian {N : ℕ} (Q : Model N) (w : Disorder N) :
    parity Q (hamiltonian Q w)=hamiltonian Q w := by
  unfold hamiltonian parity
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro A hA
  rw [mul_smul_comm, smul_mul_assoc]
  change (w A : ℂ) • parity Q (rawString Q A.1) = _
  rw [parity_rawString]
  norm_num [A.2]

lemma parityMatrix_commute_hamiltonian {N : ℕ} (Q : Model N) (w : Disorder N) :
    Commute (parityMatrix Q) (hamiltonian Q w) := by
  have h := congrArg (fun A : Mat (SiteHilbert N) ↦ A * parityMatrix Q) (parity_hamiltonian Q w)
  change parityMatrix Q * hamiltonian Q w=hamiltonian Q w * parityMatrix Q
  simpa only [parity, mul_assoc, parityMatrix_sq, mul_one] using h

lemma parityMatrix_commute_mexp {N : ℕ} (Q : Model N) (w : Disorder N) (a : ℂ) :
    Commute (parityMatrix Q) (mexp (a • hamiltonian Q w)) :=
  ((parityMatrix_commute_hamiltonian Q w).smul_right a).exp_right

lemma parity_mexp {N : ℕ} (Q : Model N) (w : Disorder N) (a : ℂ) :
    parity Q (mexp (a • hamiltonian Q w))=mexp (a • hamiltonian Q w) := by
  unfold parity
  rw [(parityMatrix_commute_mexp Q w a).eq, mul_assoc, parityMatrix_sq, mul_one]

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

lemma parity_imaginary {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) (i : Fin N) :
    parity Q (imaginary Q w s i)=-imaginary Q w s i := by
  unfold imaginary
  rw [parity_mul, parity_mul, parity_mexp, parity_mexp, parity_gamma]
  simp only [mul_neg, neg_mul]

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma applySuper_b_expression {ι : Type} [Fintype ι] [DecidableEq ι]
    (A P X : Mat ι) :
    applySuper (super (fun Y ↦ (1/2 : ℂ) • (A*Y - P*Y*P*Aᴴ))) X =
      (1/2 : ℂ) • (A*X - P*X*P*Aᴴ) := by
  let F : Mat ι →L[ℂ] Mat ι := (1/2 : ℂ) •
    (leftAct A - (rightAct Aᴴ).comp ((rightAct P).comp (leftAct P)))
  exact applySuper_super F.toLinearMap X

lemma bMap_apply {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (i : Fin N) (X : Mat (SiteHilbert N)) :
    applySuper (bMap Q w β i) X =
      (1/2 : ℂ) • (imaginary Q w (β/4) i * X - parity Q X * (imaginary Q w (β/4) i)ᴴ) :=
  applySuper_b_expression _ _ _


end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
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

lemma hsInner_parity {N : ℕ} (Q : Model N) (X Y : Mat (SiteHilbert N)) :
    hsInner (parity Q X) Y=hsInner X (parity Q Y) := by
  unfold parity
  rw [hsInner_rightMul, hsInner_leftMul, (parityMatrix_hermitian Q).eq]
  rw [mul_assoc]


end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma applySuper_add {ι : Type} [Fintype ι] [DecidableEq ι] (T U : Super ι) (X : Mat ι) :
    applySuper (T+U) X=applySuper T X+applySuper U X := (evalSuper X).map_add T U

@[simp] lemma applySuper_zero {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) :
    applySuper (0 : Super ι) X=0 := (evalSuper X).map_zero

lemma parity_smul {N : ℕ} (Q : Model N) (z : ℂ) (X : Mat (SiteHilbert N)) :
    parity Q (z • X)=z • parity Q X := by simp only [parity, mul_smul_comm, smul_mul_assoc]

lemma parity_sub {N : ℕ} (Q : Model N) (X Y : Mat (SiteHilbert N)) :
    parity Q (X-Y)=parity Q X-parity Q Y := by simp only [parity, mul_sub, sub_mul]

lemma parity_add {N : ℕ} (Q : Model N) (X Y : Mat (SiteHilbert N)) :
    parity Q (X+Y)=parity Q X+parity Q Y := by simp only [parity, mul_add, add_mul]


end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped ComplexConjugate

lemma diagonal_gap_decay {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ev : ι → ℝ) (r x : ι → ℂ) (rate t : ℝ) (hrate : 0 < rate) (ht : 0 ≤ t)
    (hr : ∀ i, (ev i : ℂ)*r i=0)
    (hgap : ∀ y : ι → ℂ, star r ⬝ᵥ y=0 →
      rate * (∑ i, ‖y i‖^2) ≤ ∑ i, ev i * ‖y i‖^2)
    (hx : star r ⬝ᵥ x=0) :
    (∑ i, ‖(Real.exp (-t*ev i) : ℂ) * x i‖^2) ≤
      (Real.exp (-rate*t))^2 * ∑ i, ‖x i‖^2 := by
  have hrzero (i : ι) (hi : ev i ≠ 0) : r i=0 :=
    (mul_eq_zero.mp (hr i)).resolve_left (by exact_mod_cast hi)
  let z : ι → ℂ := fun i ↦ if ev i=0 then x i else 0
  have hzortho : star r ⬝ᵥ z=0 := by
    calc
      _ = star r ⬝ᵥ x := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases he : ev i=0
        · simp [z, he]
        · simp [z, he, hrzero i he]
      _ = 0 := hx
  have hzquad : (∑ i, ev i * ‖z i‖^2)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases he : ev i=0 <;> simp [z, he]
  have hzsum : (∑ i, ‖z i‖^2)=0 := by
    have h := hgap z hzortho
    rw [hzquad] at h
    have hn : 0 ≤ ∑ i, ‖z i‖^2 := by positivity
    nlinarith
  have hxzero (i : ι) (hi : ev i=0) : x i=0 := by
    have hs : ‖z i‖^2 ≤ ∑ j, ‖z j‖^2 :=
      Finset.single_le_sum (f := fun j ↦ ‖z j‖^2) (fun j hj ↦ sq_nonneg _) (Finset.mem_univ i)
    rw [hzsum] at hs
    have hzi : z i=0 := by simpa only [sq_nonpos_iff, norm_eq_zero] using hs
    simpa only [z, if_pos hi] using hzi
  have hev (i : ι) (hi : ev i ≠ 0) : rate ≤ ev i := by
    have ho : star r ⬝ᵥ Pi.single i (1 : ℂ)=0 := by simp [dotProduct, Pi.single_apply, apply_ite, hrzero i hi]
    have h := hgap (Pi.single i (1 : ℂ)) ho
    simpa [Pi.single_apply, apply_ite, eq_comm] using h
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hzero : ev i=0
  · simp [hxzero i hzero]
  · rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    have he := hev i hzero
    nlinarith


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
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

lemma basis_qform {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℝ)
    (hdiag : ∀ x i, b.repr (T x) i = (ev i : ℂ) * b.repr x i) (x : E) :
    (inner ℂ x (T x)).re = ∑ i, ev i * ‖b.repr x i‖^2 := by
  rw [← b.repr.inner_map_map x (T x), EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, hdiag]
  apply Finset.sum_congr rfl
  intro i hi
  change ((ev i : ℂ) * b.repr x i * conj (b.repr x i)).re = _
  rw [mul_assoc, mul_comm (b.repr x i), ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.normSq_eq_norm_sq]

lemma basis_gap_decay {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℝ)
    (hdiag : ∀ x i, b.repr (T x) i = (ev i : ℂ) * b.repr x i)
    (r x : E) (rate t : ℝ) (hrate : 0 < rate) (ht : 0 ≤ t) (hr : T r=0)
    (hgap : ∀ y : E, inner ℂ r y=0 → rate * ‖y‖^2 ≤ (inner ℂ y (T y)).re)
    (hx : inner ℂ r x=0) :
    ‖(NormedSpace.exp (((-t : ℝ) : ℂ) • T)) x‖ ≤ Real.exp (-rate*t) * ‖x‖ := by
  have hroot (i : ι) : (ev i : ℂ) * b.repr r i=0 := by
    rw [← hdiag, hr, map_zero]
    rfl
  have hgapdiag (y : ι → ℂ) (hy : star (fun i ↦ b.repr r i) ⬝ᵥ y=0) :
      rate * (∑ i, ‖y i‖^2) ≤ ∑ i, ev i * ‖y i‖^2 := by
    let Y := b.repr.symm (WithLp.toLp 2 y)
    have hY : inner ℂ r Y=0 := by
      rw [← b.repr.inner_map_map r Y]
      simpa [Y, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hy
    have h := hgap Y hY
    rw [basis_qform b T ev hdiag, ← b.repr.norm_map Y, EuclideanSpace.norm_sq_eq] at h
    simpa only [Y, LinearIsometryEquiv.apply_symm_apply, WithLp.ofLp_toLp] using h
  have hxdiag : star (fun i ↦ b.repr r i) ⬝ᵥ (fun i ↦ b.repr x i)=0 := by
    rw [← b.repr.inner_map_map r x] at hx
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hx
  have hdecay := diagonal_gap_decay ev (fun i ↦ b.repr r i) (fun i ↦ b.repr x i)
    rate t hrate ht hroot hgapdiag hxdiag
  have hsdiag : ∀ y i, b.repr ((((-t : ℝ) : ℂ) • T) y) i =
      (((-t : ℝ) : ℂ) * (ev i : ℂ)) * b.repr y i := by
    intro y i
    change b.repr (((-t : ℝ) : ℂ) • T y) i = _
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, hdiag, mul_assoc]
  have hcoord (i : ι) : b.repr ((NormedSpace.exp (((-t : ℝ) : ℂ) • T)) x) i =
      (Real.exp (-t*ev i) : ℂ) * b.repr x i := by
    have h := repr_exp_apply b (((-t : ℝ) : ℂ) • T)
      (fun i ↦ (((-t : ℝ) : ℂ) * (ev i : ℂ))) hsdiag x i
    simpa only [← Complex.ofReal_mul, ← Complex.ofReal_exp] using h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp
  rw [mul_pow, ← b.repr.norm_map ((NormedSpace.exp (((-t : ℝ) : ℂ) • T)) x),
    ← b.repr.norm_map x, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [hcoord]
  exact hdecay

lemma basis_exp_fixed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℂ)
    (hdiag : ∀ x i, b.repr (T x) i = ev i * b.repr x i)
    (r : E) (hr : T r=0) (a : ℂ) : (NormedSpace.exp (a • T)) r=r := by
  have hscaled : ∀ y i, b.repr ((a • T) y) i = (a * ev i) * b.repr y i := by
    intro y i
    change b.repr (a • T y) i = _
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, hdiag, mul_assoc]
  apply b.repr.injective
  apply PiLp.ext
  intro i
  rw [repr_exp_apply b (a • T) (fun i ↦ a*ev i) hscaled]
  have hroot : ev i * b.repr r i=0 := by rw [← hdiag, hr, map_zero]; rfl
  rcases mul_eq_zero.mp hroot with hi | hi <;> simp [hi]

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
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

lemma hasGap_hs_decay (T : Super ι) (r X : Mat ι) (rate t : ℝ)
    (hrate : 0 < rate) (ht : 0 ≤ t) (hg : HasGap T r rate) (hX : hsInner r X=0) :
    hs (applySuper (mexp (((-t : ℝ) : ℂ) • T)) X) ≤ Real.exp (-rate*t) * hs X := by
  have hT : T.IsHermitian := hg.1
  let A := Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) T
  have hr : A (hsVec r)=0 := by rw [← hsVec_applySuper, hg.2.2.1]; rfl
  have hgap : ∀ y : EuclideanSpace ℂ (ι × ι), inner ℂ (hsVec r) y=0 →
      rate * ‖y‖^2 ≤ (inner ℂ y (A y)).re := by
    intro y hy
    have he := hg.2.2.2 (hsUnvec y)
    rw [← hsVec_inner, hsVec_hsUnvec] at he
    have h := he hy
    change rate * hsSq (hsUnvec y) ≤ (hsInner (hsUnvec y) (applySuper T (hsUnvec y))).re at h
    rw [← hsVec_inner, hsVec_applySuper, hsVec_hsUnvec] at h
    have hn : hsSq (hsUnvec y)=‖y‖^2 := by
      have hnorm := hsVec_norm (hsUnvec y)
      rw [hsVec_hsUnvec] at hnorm
      calc
        hsSq (hsUnvec y) = (hs (hsUnvec y))^2 := (Real.sq_sqrt (hsSq_nonneg _)).symm
        _ = ‖y‖^2 := by rw [← hnorm]
    rwa [hn] at h
  have h := basis_gap_decay hT.eigenvectorBasis A hT.eigenvalues
    (hermitian_repr_apply T hT) (hsVec r) (hsVec X) rate t hrate ht hr hgap
    (by rw [hsVec_inner]; exact hX)
  rw [← hsVec_norm, ← hsVec_norm, hsVec_applySuper, euclideanAct_exp]
  have he : Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) (((-t : ℝ) : ℂ) • T) = (((-t : ℝ) : ℂ) • A) :=
    map_smul (Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ)) _ T
  rw [he]
  exact h

lemma hermitian_exp_fixed (T : Super ι) (hT : T.IsHermitian) (X : Mat ι)
    (hX : applySuper T X=0) (a : ℂ) : applySuper (mexp (a • T)) X=X := by
  apply hsVec_injective
  rw [hsVec_applySuper, euclideanAct_exp, map_smul]
  apply basis_exp_fixed hT.eigenvectorBasis
    (Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) T) (fun i ↦ (hT.eigenvalues i : ℂ))
    (hermitian_repr_apply T hT)
  rw [← hsVec_applySuper, hX]
  rfl

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped ComplexConjugate
namespace SYKFastMix.FastMixing

lemma basis_positive_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (ev : ι → ℝ)
    (hdiag : ∀ x i, b.repr (T x) i = (ev i : ℂ)*b.repr x i)
    (r : E) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x, 0 ≤ (inner ℂ x (T x)).re)
    (hsq : ∀ x, c*(inner ℂ x (T x)).re ≤ ‖T x‖^2)
    (hker : ∀ x, T x=0 ↔ ∃ z : ℂ, x=z • r)
    (x : E) (hx : inner ℂ r x=0) : c*‖x‖^2 ≤ (inner ℂ x (T x)).re := by
  have heigen (i : ι) : T (b i)=(ev i : ℂ) • b i := by
    apply b.repr.injective
    apply PiLp.ext
    intro j
    rw [hdiag, map_smul, b.repr_self]
    change (ev j : ℂ) * (Pi.single i (1 : ℂ) : ι → ℂ) j =
      (ev i : ℂ) * (Pi.single i (1 : ℂ) : ι → ℂ) j
    by_cases hji : j=i
    · subst j; rfl
    · simp [Pi.single_apply, Ne.symm hji]
  have hnorm (i : ι) : ‖b i‖=1 := b.orthonormal.norm_eq_one i
  have hq (i : ι) : (inner ℂ (b i) (T (b i))).re=ev i := by
    rw [heigen, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hevsq (i : ι) : ‖T (b i)‖^2=(ev i)^2 := by
    rw [heigen, norm_smul, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hev (i : ι) (hi : ev i ≠ 0) : c ≤ ev i := by
    have hn := hpos (b i)
    have hs := hsq (b i)
    rw [hq] at hn hs
    rw [hevsq] at hs
    have hp : 0 < ev i := lt_of_le_of_ne hn (Ne.symm hi)
    nlinarith
  have hzero (i : ι) (hi : ev i=0) : b.repr x i=0 := by
    have ht : T (b i)=0 := by rw [heigen, hi]; simp
    obtain ⟨z, hz⟩ := (hker (b i)).mp ht
    rw [b.repr_apply_apply, hz, inner_smul_left, hx, mul_zero]
  rw [basis_qform b T ev hdiag, ← b.repr.norm_map x, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases he : ev i=0
  · rw [hzero i he]
    simp
  · exact mul_le_mul_of_nonneg_right (hev i he) (sq_nonneg _)

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma quadratic_inequality_hasGap {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Super ι) (r : Mat ι) (c : ℝ) (hc : 0 < c) (hT : T.IsHermitian)
    (hpos : ∀ X, 0 ≤ qform T X) (hker : KernelSpan T r)
    (hsq : ∀ X, c*qform T X ≤ qform (T*T) X) : HasGap T r c := by
  have hr : applySuper T r=0 := (hker r).mpr ⟨1, by rw [one_smul]⟩
  refine ⟨hT, hpos, hr, ?_⟩
  intro X hX
  let A := Matrix.toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) T
  have heq (Y : Mat ι) : qform T Y=(inner ℂ (hsVec Y) (A (hsVec Y))).re := by
    rw [← hsVec_applySuper, hsVec_inner]
    rfl
  have hp : ∀ y : EuclideanSpace ℂ (ι × ι), 0 ≤ (inner ℂ y (A y)).re := by
    intro y
    have h := hpos (hsUnvec y)
    rw [heq, hsVec_hsUnvec] at h
    exact h
  have hs : ∀ y : EuclideanSpace ℂ (ι × ι), c*(inner ℂ y (A y)).re ≤ ‖A y‖^2 := by
    intro y
    have h := hsq (hsUnvec y)
    have hmult : T*T=Tᴴ*T := by rw [hT.eq]
    rw [hmult, qform_adj_mul, heq, ← hsVec_norm_sq, hsVec_applySuper, hsVec_hsUnvec] at h
    exact h
  have hroot : A (hsVec r)=0 := by rw [← hsVec_applySuper, hr]; rfl
  have hk : ∀ y : EuclideanSpace ℂ (ι × ι), A y=0 ↔ ∃ z : ℂ, y=z • hsVec r := by
    intro y
    constructor
    · intro hy
      have hY : applySuper T (hsUnvec y)=0 := by
        apply hsVec_injective
        rw [hsVec_applySuper, hsVec_hsUnvec]
        exact hy
      obtain ⟨z, hz⟩ := (hker (hsUnvec y)).mp hY
      refine ⟨z, ?_⟩
      have h := congrArg hsVec hz
      rwa [hsVec_hsUnvec, hsVec_smul] at h
    · rintro ⟨z, rfl⟩
      rw [map_smul, hroot, smul_zero]
  have h := basis_positive_gap hT.eigenvectorBasis A hT.eigenvalues (hermitian_repr_apply T hT)
    (hsVec r) c hc hp hs hk (hsVec X) (by rw [hsVec_inner]; exact hX)
  rw [hsVec_norm_sq, ← heq] at h
  exact h

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace SYKFastMix.FastMixing

lemma hermitian_similar_near_identity {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B S Sinv : Mat ι) (hA : A.IsHermitian) (hS : S*Sinv=1) (hiS : Sinv*S=1)
    (hB : B=Sinv*A*S) (δ : ℝ) (hδ : ‖B-1‖ ≤ δ) :
    ∀ x : EuclideanSpace ℂ ι, (1-δ)*‖x‖^2 ≤
      (inner ℂ x ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x)).re := by
  let L := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
  have heA (i : ι) : L A (hA.eigenvectorBasis i)=(hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    change (A *ᵥ (hA.eigenvectorBasis i : ι → ℂ)) j = _
    rw [hA.mulVec_eigenvectorBasis]
    rfl
  have hevlower (i : ι) : 1-δ ≤ hA.eigenvalues i := by
    let v := hA.eigenvectorBasis i
    let y := L Sinv v
    have hcancel : L S y=v := by
      change L S (L Sinv v)=v
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, hS, map_one]
      rfl
    have hy : y ≠ 0 := by
      intro hy
      rw [hy, map_zero] at hcancel
      exact hA.eigenvectorBasis.orthonormal.ne_zero i hcancel.symm
    have heig : L B y=(hA.eigenvalues i : ℂ) • y := by
      rw [hB, map_mul, map_mul]
      change L Sinv (L A (L S y))=_
      rw [hcancel, heA, map_smul]
    have hdiff : L (B-1) y=((hA.eigenvalues i-1 : ℝ) : ℂ) • y := by
      rw [map_sub, map_one]
      change L B y-y=_
      rw [heig, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    have hn := (L (B-1)).le_opNorm y
    rw [hdiff, norm_smul, Complex.norm_real, Real.norm_eq_abs] at hn
    change |hA.eigenvalues i-1| * ‖y‖ ≤ ‖B-1‖ * ‖y‖ at hn
    have hbound : |hA.eigenvalues i-1| ≤ δ := by
      apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hy)).mp
      exact hn.trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))
    have h := (abs_le.mp hbound).1
    linarith
  intro x
  rw [basis_qform hA.eigenvectorBasis (L A) hA.eigenvalues (hermitian_repr_apply A hA),
    ← hA.eigenvectorBasis.repr.norm_map x, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_right (hevlower i) (sq_nonneg _)

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

def subblock {I ι : Type} (M : Matrix (I × ι) (I × ι) ℂ) (i j : I) : Mat ι :=
  Matrix.of (fun a b ↦ M (i,a) (j,b))

def stackRows {I ι : Type} (X : I → Mat ι) : Matrix (I × ι) ι ℂ :=
  Matrix.of (fun p k ↦ X p.1 p.2 k)

lemma trace_rectangular_lower_bound {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m m ℂ) (Z : Matrix m n ℂ) (c : ℝ)
    (hM : ∀ x : EuclideanSpace ℂ m, c*‖x‖^2 ≤
      (inner ℂ x ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) M) x)).re) :
    c*(∑ j, ∑ i, ‖Z i j‖^2) ≤ (Matrix.trace (Zᴴ*M*Z)).re := by
  let col (j : n) : EuclideanSpace ℂ m := WithLp.toLp 2 (fun i ↦ Z i j)
  have ht : (Matrix.trace (Zᴴ*M*Z)).re =
      ∑ j, (inner ℂ (col j) ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) M) (col j))).re := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, col,
      Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_toLp, Matrix.mulVec, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [mul_comm]
  rw [ht, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  simpa only [EuclideanSpace.norm_sq_eq, col, WithLp.ofLp_toLp] using hM (col j)

lemma hs_block_form_eq_trace {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι]
    (M : Matrix (I × ι) (I × ι) ℂ) (X : I → Mat ι) :
    (∑ i, ∑ j, hsInner (X i) (subblock M i j * X j)) =
      Matrix.trace ((stackRows X)ᴴ * M * stackRows X) := by
  rw [Matrix.mul_assoc]
  simp only [hsInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.mul_sum, subblock, stackRows, Matrix.of_apply]
  calc
    _ = ∑ i : I, ∑ k : ι, ∑ j : I, ∑ a : ι, ∑ b : ι,
        star (X i a k) * (M (i,a) (j,b) * X j b k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k : ι, ∑ i : I, ∑ j : I, ∑ a : ι, ∑ b : ι,
        star (X i a k) * (M (i,a) (j,b) * X j b k) := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]

lemma hs_block_form_lower_bound {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq I] [DecidableEq ι]
    (M : Matrix (I × ι) (I × ι) ℂ) (c : ℝ)
    (hM : ∀ x : EuclideanSpace ℂ (I × ι), c*‖x‖^2 ≤
      (inner ℂ x ((Matrix.toEuclideanCLM (n := I × ι) (𝕜 := ℂ) M) x)).re)
    (X : I → Mat ι) :
    c*(∑ i, hsSq (X i)) ≤ (∑ i, ∑ j, hsInner (X i) (subblock M i j * X j)).re := by
  rw [hs_block_form_eq_trace]
  have h := trace_rectangular_lower_bound M (stackRows X) c hM
  have he : (∑ k : ι, ∑ p : I × ι, ‖X p.1 p.2 k‖^2) = ∑ i, hsSq (X i) := by
    simp only [Fintype.sum_prod_type, hsSq_eq_sum_columns]
    rw [Finset.sum_comm]
  simpa only [stackRows, Matrix.of_apply, he] using h

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
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

lemma repeatBlock_sandwich {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq I]
    (A B : Mat ι) (M : Mat (I × ι)) (i j : I) :
    subblock (repeatBlock A * M * repeatBlock B) i j=A*subblock M i j*B := by
  ext a b
  simp [subblock, repeatBlock, Matrix.mul_apply, Fintype.sum_prod_type]

def mixedJacobian {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) : Mat (Fin N × SiteHilbert N) :=
  Matrix.of (fun a b ↦ ((1/2 : ℂ) •
    anticomm (imaginary Q w (β/4) a.1) ((imaginary Q w (β/4) b.1)ᴴ)) a.2 b.2)

lemma mixedJacobian_hermitian {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) :
    (mixedJacobian Q w β).IsHermitian := by
  unfold Matrix.IsHermitian
  ext a b
  change (((1/2 : ℂ) • anticomm (imaginary Q w (β/4) b.1)
    ((imaginary Q w (β/4) a.1)ᴴ))ᴴ) a.2 b.2 = _
  simp only [Matrix.conjTranspose_smul, anticomm, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, map_div₀, map_one, map_ofNat]
  have hz : star (1/2 : ℂ)=(1/2 : ℂ) := by
    change conj (1/2 : ℂ)=(1/2 : ℂ)
    norm_num [map_ofNat]
  rw [hz]
  rfl

lemma mixedJacobian_similarity {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) :
    let B := mexp (((β/4 : ℝ) : ℂ) • hamiltonian Q w)
    let C := mexp (((-(β/4) : ℝ) : ℂ) • hamiltonian Q w)
    mixedJacobian Q w β = repeatBlock B * jacobian Q w (β/2) * repeatBlock C := by
  dsimp only
  let H := hamiltonian Q w
  let B := mexp (((β/4 : ℝ) : ℂ) • H)
  let C := mexp (((-(β/4) : ℝ) : ℂ) • H)
  have hBC : B*C=1 := by
    change mexp (((β/4 : ℝ) : ℂ) • H) * mexp (((-(β/4) : ℝ) : ℂ) • H)=1
    rw [mexp_smul_add]
    have he : ((β/4 : ℝ) : ℂ)+((-(β/4) : ℝ) : ℂ)=0 := by push_cast; ring
    rw [he]; simp [mexp]
  have hCC : C*C=mexp (((-(β/2) : ℝ) : ℂ) • H) := by
    change mexp (((-(β/4) : ℝ) : ℂ) • H) * mexp (((-(β/4) : ℝ) : ℂ) • H)=_
    rw [mexp_smul_add]
    congr 2
    push_cast
    ring
  have hBB : B*B=mexp (((β/2 : ℝ) : ℂ) • H) := by
    change mexp (((β/4 : ℝ) : ℂ) • H) * mexp (((β/4 : ℝ) : ℂ) • H)=_
    rw [mexp_smul_add]
    congr 2
    push_cast
    ring
  have him (i : Fin N) : imaginary Q w (β/4) i=C*Q.γ i*B := by
    simp only [imaginary, C, B, H, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  have himstar (i : Fin N) : (imaginary Q w (β/4) i)ᴴ=B*Q.γ i*C := by
    rw [imaginary_conjTranspose]
    simp only [imaginary, C, B, H, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, neg_neg]
  have hhalf (i : Fin N) : imaginary Q w (β/2) i=(C*C)*Q.γ i*(B*B) := by
    rw [hCC, hBB]
    simp only [imaginary, H, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hp (i j : Fin N) : (1/2 : ℂ) •
      anticomm (imaginary Q w (β/4) i) ((imaginary Q w (β/4) j)ᴴ) =
      B*((1/2 : ℂ) • anticomm (Q.γ j) (imaginary Q w (β/2) i))*C := by
    rw [himstar, him, hhalf, mul_smul_comm, smul_mul_assoc]
    congr 1
    unfold anticomm
    calc
      _ = (B*C)*C*Q.γ i*(B*B)*Q.γ j*C + B*Q.γ j*(C*C)*Q.γ i*B*(B*C) := by
        rw [hBC]
        noncomm_ring
      _ = _ := by noncomm_ring
  apply Matrix.ext
  intro a b
  have h := congrArg (fun A : Mat (SiteHilbert N) ↦ A a.2 b.2) (hp a.1 b.1)
  change mixedJacobian Q w β a b =
    ((repeatBlock (I := Fin N) B * jacobian Q w (β/2) * repeatBlock (I := Fin N) C) : Mat (Fin N × SiteHilbert N)) a b
  change _ = subblock (repeatBlock (I := Fin N) B * jacobian Q w (β/2) * repeatBlock (I := Fin N) C) a.1 b.1 a.2 b.2
  rw [repeatBlock_sandwich]
  exact h

lemma mixedJacobian_coercive {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (hjac : SYKEdge.opNorm (jacobian Q w (β/2)-1) ≤ 1/4) :
    ∀ x : EuclideanSpace ℂ (Fin N × SiteHilbert N), (3/4 : ℝ)*‖x‖^2 ≤
      (inner ℂ x ((Matrix.toEuclideanCLM (n := Fin N × SiteHilbert N) (𝕜 := ℂ)
        (mixedJacobian Q w β)) x)).re := by
  let B := mexp (((β/4 : ℝ) : ℂ) • hamiltonian Q w)
  let C := mexp (((-(β/4) : ℝ) : ℂ) • hamiltonian Q w)
  have hBC : B*C=1 := by
    change mexp (((β/4 : ℝ) : ℂ) • hamiltonian Q w) * mexp (((-(β/4) : ℝ) : ℂ) • hamiltonian Q w)=1
    rw [mexp_smul_add]
    have he : ((β/4 : ℝ) : ℂ)+((-(β/4) : ℝ) : ℂ)=0 := by push_cast; ring
    rw [he]; simp [mexp]
  have hCB : C*B=1 := by
    change mexp (((-(β/4) : ℝ) : ℂ) • hamiltonian Q w) * mexp (((β/4 : ℝ) : ℂ) • hamiltonian Q w)=1
    rw [mexp_smul_add]
    have he : ((-(β/4) : ℝ) : ℂ)+((β/4 : ℝ) : ℂ)=0 := by push_cast; ring
    rw [he]; simp [mexp]
  have hS : repeatBlock (I := Fin N) B * repeatBlock C=1 := by rw [repeatBlock_mul, hBC, repeatBlock_one]
  have hiS : repeatBlock (I := Fin N) C * repeatBlock B=1 := by rw [repeatBlock_mul, hCB, repeatBlock_one]
  have hs : mixedJacobian Q w β=repeatBlock B*jacobian Q w (β/2)*repeatBlock C :=
    mixedJacobian_similarity Q w β
  have hsim : jacobian Q w (β/2)=repeatBlock C*mixedJacobian Q w β*repeatBlock B := by
    rw [hs]
    symm
    calc
      _ = (repeatBlock C*repeatBlock B)*jacobian Q w (β/2)*(repeatBlock C*repeatBlock B) := by noncomm_ring
      _ = _ := by rw [hiS, one_mul, mul_one]
  have h := hermitian_similar_near_identity (mixedJacobian Q w β) (jacobian Q w (β/2))
    (repeatBlock B) (repeatBlock C) (mixedJacobian_hermitian Q w β) hS hiS hsim (1/4) hjac
  norm_num at h
  exact h

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma fermionic_square_identity {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι]
    (B : I → Mat ι) (hB : ∀ i j, B i * B j+B j * B i=0) :
    (∑ i, (B i)ᴴ * B i) * (∑ i, (B i)ᴴ * B i) =
      (∑ i, ∑ j, (B i)ᴴ * (B i * (B j)ᴴ + (B j)ᴴ * B i) * B j) +
      ∑ i, (B i)ᴴ * (∑ j, (B j)ᴴ * B j) * B i := by
  have he (i j : I) : (B i)ᴴ * B i * ((B j)ᴴ * B j) =
      (B i)ᴴ * (B i * (B j)ᴴ + (B j)ᴴ * B i) * B j +
        (B i)ᴴ * (B j)ᴴ * B j * B i := by
    symm
    calc
      _ = (B i)ᴴ * B i * ((B j)ᴴ * B j) + (B i)ᴴ * (B j)ᴴ * (B i * B j+B j*B i) := by noncomm_ring
      _ = _ := by rw [hB]; simp
  calc
    _ = ∑ i, ∑ j, (B i)ᴴ * B i * ((B j)ᴴ * B j) := by rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ((B i)ᴴ * (B i * (B j)ᴴ + (B j)ᴴ * B i) * B j +
        (B i)ᴴ * (B j)ᴴ * B j * B i) := by simp_rw [he]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      noncomm_ring

lemma qform_sum {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι]
    (T : I → Super ι) (X : Mat ι) : qform (∑ i, T i) X=∑ i, qform (T i) X := by
  unfold qform
  change ((hsInnerLinear X) ((evalSuper X) (∑ i, T i))).re = _
  rw [map_sum, map_sum, Complex.re_sum]
  rfl

lemma qform_adj_left_right {ι : Type} [Fintype ι] [DecidableEq ι]
    (S T U : Super ι) (X : Mat ι) :
    qform (Sᴴ*T*U) X=(hsInner (applySuper S X) (applySuper T (applySuper U X))).re := by
  unfold qform
  rw [applySuper_mul, applySuper_mul, ← hsInner_applySuper_adjoint]

lemma qform_sum_adj_nonneg {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι]
    (B : I → Super ι) (X : Mat ι) : 0 ≤ qform (∑ i, (B i)ᴴ*B i) X := by
  rw [qform_sum_adj_mul]
  exact Finset.sum_nonneg fun i hi ↦ hsSq_nonneg _

lemma fermionic_square_coercive {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι]
    (B : I → Super ι) (hB : ∀ i j, B i * B j+B j * B i=0) (c : ℝ)
    (hCAR : ∀ Y : I → Mat ι, c*(∑ i, hsSq (Y i)) ≤
      (∑ i, ∑ j, hsInner (Y i) (applySuper (B i*(B j)ᴴ+(B j)ᴴ*B i) (Y j))).re) :
    ∀ X, c*qform (∑ i, (B i)ᴴ*B i) X ≤
      qform ((∑ i, (B i)ᴴ*B i)*(∑ i, (B i)ᴴ*B i)) X := by
  intro X
  have h := hCAR (fun i ↦ applySuper (B i) X)
  rw [← qform_sum_adj_mul] at h
  simp only [Complex.re_sum] at h
  rw [fermionic_square_identity B hB]
  have hqadd (S T : Super ι) : qform (S+T) X=qform S X+qform T X := by
    simp only [qform, applySuper_add, hsInner_add_right, Complex.add_re]
  rw [hqadd, qform_sum, qform_sum]
  simp_rw [qform_sum, qform_adj_left_right]
  have hn : 0 ≤ ∑ i, (hsInner (applySuper (B i) X)
      (applySuper (∑ j, (B j)ᴴ*B j) (applySuper (B i) X))).re := by
    exact Finset.sum_nonneg fun i hi ↦ qform_sum_adj_nonneg B (applySuper (B i) X)
  rw [qform_sum] at h
  linarith

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma fermionic_sum_squares_gap {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι]
    (B : I → Super ι) (r : Mat ι) (c : ℝ) (hc : 0 < c)
    (hB : ∀ i j, B i*B j+B j*B i=0)
    (hCAR : ∀ Y : I → Mat ι, c*(∑ i, hsSq (Y i)) ≤
      (∑ i, ∑ j, hsInner (Y i) (applySuper (B i*(B j)ᴴ+(B j)ᴴ*B i) (Y j))).re)
    (hker : ∀ X, (∀ i, applySuper (B i) X=0) ↔ ∃ z : ℂ, X=z • r) :
    HasGap (∑ i, (B i)ᴴ*B i) r c := by
  have hherm : (∑ i, (B i)ᴴ*B i).IsHermitian := by
    unfold Matrix.IsHermitian
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hk : KernelSpan (∑ i, (B i)ᴴ*B i) r := by
    intro X
    rw [applySuper_sum_adj_mul_eq_zero_iff]
    exact hker X
  exact quadratic_inequality_hasGap _ r c hc hherm (qform_sum_adj_nonneg B) hk
    (fermionic_square_coercive B hB c hCAR)

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma hsInner_right_cycle {ι : Type} [Fintype ι] [DecidableEq ι] (X Y A : Mat ι) :
    hsInner X (Y*A)=hsInner Yᴴ (A*Xᴴ) := by
  unfold hsInner
  rw [Matrix.conjTranspose_conjTranspose]
  calc
    _ = Matrix.trace ((Y*A)*Xᴴ) := Matrix.trace_mul_comm _ _
    _ = _ := by rw [mul_assoc]

lemma hs_block_right_form {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι]
    (M : Mat (I × ι)) (Y : I → Mat ι) :
    (∑ i, ∑ j, hsInner (Y i) (Y j * subblock M j i)) =
      ∑ i, ∑ j, hsInner (Y i)ᴴ (subblock M i j * (Y j)ᴴ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact hsInner_right_cycle _ _ _

lemma hs_block_symmetric_form {I ι : Type} [Fintype I] [Fintype ι] [DecidableEq ι]
    (M : Mat (I × ι)) (Y : I → Mat ι) :
    (∑ i, ∑ j, hsInner (Y i) ((1/2 : ℂ) • (subblock M i j * Y j + Y j * subblock M j i))).re =
      (1/2 : ℝ) * ((∑ i, ∑ j, hsInner (Y i) (subblock M i j * Y j)).re +
        (∑ i, ∑ j, hsInner (Y i)ᴴ (subblock M i j * (Y j)ᴴ)).re) := by
  rw [← hs_block_right_form]
  simp only [hsInner_smul_right, hsInner_add_right, Complex.re_sum, Complex.mul_re,
    Complex.add_re]
  norm_num
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

lemma mixedJacobian_subblock {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (i j : Fin N) :
    subblock (mixedJacobian Q w β) i j = (1/2 : ℂ) •
      anticomm (imaginary Q w (β/4) i) ((imaginary Q w (β/4) j)ᴴ) := by
  ext a b
  rfl

lemma bMap_mixed_subblock {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β)
    (i j : Fin N) (X : Mat (SiteHilbert N)) :
    applySuper (bMap Q w β i * (bMap Q w β j)ᴴ + (bMap Q w β j)ᴴ * bMap Q w β i) X =
      (1/2 : ℂ) • (subblock (mixedJacobian Q w β) i j * X + X * subblock (mixedJacobian Q w β) j i) := by
  rw [(lemma_7 Q w β hβ).2.1 i j X, mixedJacobian_subblock, mixedJacobian_subblock,
    smul_mul_assoc, mul_smul_comm, ← smul_add, smul_smul]
  norm_num

lemma bMap_CAR_coercive {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β)
    (hjac : SYKEdge.opNorm (jacobian Q w (β/2)-1) ≤ 1/4) :
    ∀ Y : Fin N → Mat (SiteHilbert N), (3/4 : ℝ)*(∑ i, hsSq (Y i)) ≤
      (∑ i, ∑ j, hsInner (Y i)
        (applySuper (bMap Q w β i * (bMap Q w β j)ᴴ + (bMap Q w β j)ᴴ * bMap Q w β i) (Y j))).re := by
  intro Y
  have hM := mixedJacobian_coercive Q w β hjac
  have hL := hs_block_form_lower_bound (mixedJacobian Q w β) (3/4) hM Y
  have hR := hs_block_form_lower_bound (mixedJacobian Q w β) (3/4) hM (fun i ↦ (Y i)ᴴ)
  simp_rw [hsSq_conjTranspose] at hR
  simp_rw [bMap_mixed_subblock Q w β hβ]
  rw [hs_block_symmetric_form]
  linarith

lemma auxiliary_bMap_gap {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β)
    (hjac : SYKEdge.opNorm (jacobian Q w (β/2)-1) ≤ 1/4) :
    HasGap (∑ i, (bMap Q w β i)ᴴ*bMap Q w β i) (gibbsRoot (hamiltonian Q w) β) (3/4) := by
  exact fermionic_sum_squares_gap (bMap Q w β) (gibbsRoot (hamiltonian Q w) β) (3/4) (by norm_num)
    (lemma_7 Q w β hβ).1 (bMap_CAR_coercive Q w β hβ hjac) (lemma_7 Q w β hβ).2.2

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma hsInner_add_left {ι : Type} [Fintype ι] [DecidableEq ι] (X Y Z : Mat ι) :
    hsInner (X+Y) Z=hsInner X Z+hsInner Y Z := by simp [hsInner, Matrix.conjTranspose_add, add_mul]

lemma hsSq_add_of_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι] (X Y : Mat ι)
    (hXY : hsInner X Y=0) : hsSq (X+Y)=hsSq X+hsSq Y := by
  have hYX : hsInner Y X=0 := by rw [hsInner_conj_symm, hXY]; simp
  unfold hsSq
  rw [hsInner_add_left, hsInner_add_right, hsInner_add_right, hXY, hYX]
  simp

lemma even_odd_orthogonal {N : ℕ} (Q : Model N) (X Y : Mat (SiteHilbert N))
    (hX : parity Q X=X) (hY : parity Q Y=-Y) : hsInner X Y=0 := by
  have h : hsInner X Y=-hsInner X Y := by
    calc
      _ = hsInner (parity Q X) Y := by rw [hX]
      _ = hsInner X (parity Q Y) := hsInner_parity Q X Y
      _ = _ := by rw [hY, hsInner_neg_right]
  linear_combination (1/2 : ℂ)*h

lemma hsSq_right_parity {N : ℕ} (Q : Model N) (X : Mat (SiteHilbert N)) :
    hsSq (X*parityMatrix Q)=hsSq X := by
  unfold hsSq
  rw [hsInner_rightMul, (parityMatrix_hermitian Q).eq, mul_assoc, parityMatrix_sq, mul_one]

lemma parity_right_parity {N : ℕ} (Q : Model N) (X : Mat (SiteHilbert N)) :
    parity Q (X*parityMatrix Q)=parity Q X*parityMatrix Q := by
  unfold parity
  noncomm_ring

lemma parity_gibbsRoot {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) :
    parity Q (gibbsRoot (hamiltonian Q w) β)=gibbsRoot (hamiltonian Q w) β := by
  unfold gibbsRoot
  rw [parity_smul]
  have h := parity_mexp Q w (-((β : ℂ)/2))
  rw [h]

lemma cMap_apply {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (i : Fin N) (X : Mat (SiteHilbert N)) :
    applySuper (cMap Q w β i) X=(1/2 : ℂ) •
      (imaginary Q w (β/4) i * X-X*(imaginary Q w (β/4) i)ᴴ) := by
  let A := imaginary Q w (β/4) i
  exact applySuper_super ((1/2 : ℂ) • (leftAct A-rightAct Aᴴ)).toLinearMap X

lemma cMap_parity {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (i : Fin N) (X : Mat (SiteHilbert N)) :
    parity Q (applySuper (cMap Q w β i) X)=-applySuper (cMap Q w β i) (parity Q X) := by
  simp only [cMap_apply, imaginary_conjTranspose, parity_smul, parity_sub, parity_mul,
    parity_imaginary, neg_mul, mul_neg]
  module

lemma odd_parity_anticomm {N : ℕ} (Q : Model N) (A : Mat (SiteHilbert N)) (hA : parity Q A=-A) :
    parityMatrix Q*A=-(A*parityMatrix Q) := by
  have h := congrArg (fun B : Mat (SiteHilbert N) ↦ B*parityMatrix Q) hA
  simpa only [parity, mul_assoc, parityMatrix_sq, mul_one, neg_mul] using h

lemma bMap_even_eq_cMap {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (i : Fin N) (X : Mat (SiteHilbert N)) (hX : parity Q X=X) :
    applySuper (bMap Q w β i) X=applySuper (cMap Q w β i) X := by rw [bMap_apply, cMap_apply, hX]

lemma bMap_odd_parity_eq_cMap {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (i : Fin N) (X : Mat (SiteHilbert N)) (hX : parity Q X=-X) :
    applySuper (bMap Q w β i) (X*parityMatrix Q)=applySuper (cMap Q w β i) X*parityMatrix Q := by
  have hA : parityMatrix Q*(imaginary Q w (β/4) i)ᴴ =
      -((imaginary Q w (β/4) i)ᴴ * parityMatrix Q) := by
    apply odd_parity_anticomm
    rw [imaginary_conjTranspose, parity_imaginary]
  rw [bMap_apply, cMap_apply, parity_right_parity, hX, neg_mul, smul_mul_assoc]
  congr 1
  calc
    _ = imaginary Q w (β/4) i*X*parityMatrix Q+X*(parityMatrix Q*(imaginary Q w (β/4) i)ᴴ) := by noncomm_ring
    _ = _ := by rw [hA]; noncomm_ring

lemma unfiltered_form_bound {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β)
    (hjac : SYKEdge.opNorm (jacobian Q w (β/2)-1) ≤ 1/4) :
    ∀ X, hsInner (gibbsRoot (hamiltonian Q w) β) X=0 →
      (3/4 : ℝ)*hsSq X ≤ qform (unfilteredK Q w β) X := by
  intro X hX
  let r := gibbsRoot (hamiltonian Q w) β
  let E := (1/2 : ℂ) • (X+parity Q X)
  let O := (1/2 : ℂ) • (X-parity Q X)
  have hsum : E+O=X := by dsimp [E, O]; module
  have hE : parity Q E=E := by
    dsimp only [E]
    rw [parity_smul, parity_add, parity_involution]
    congr 1
    abel
  have hO : parity Q O=-O := by
    dsimp only [O]
    rw [parity_smul, parity_sub, parity_involution]
    module
  have hr : parity Q r=r := parity_gibbsRoot Q w β
  have hEr : hsInner r E=0 := by
    have hp : hsInner r (parity Q X)=0 := by rw [← hsInner_parity, hr]; exact hX
    dsimp only [E]
    rw [hsInner_smul_right, hsInner_add_right, hX, hp]
    simp
  have hOP : parity Q (O*parityMatrix Q)=-(O*parityMatrix Q) := by rw [parity_right_parity, hO, neg_mul]
  have hOPr : hsInner r (O*parityMatrix Q)=0 := even_odd_orthogonal Q r _ hr hOP
  have hgap := auxiliary_bMap_gap Q w β hβ hjac
  have hEg := hgap.2.2.2 E hEr
  have hOg := hgap.2.2.2 (O*parityMatrix Q) hOPr
  rw [qform_sum_adj_mul] at hEg hOg
  simp_rw [bMap_even_eq_cMap Q w β _ E hE] at hEg
  simp_rw [bMap_odd_parity_eq_cMap Q w β _ O hO, hsSq_right_parity] at hOg
  have hEO : hsInner E O=0 := even_odd_orthogonal Q E O hE hO
  have hout (i : Fin N) : hsInner (applySuper (cMap Q w β i) E) (applySuper (cMap Q w β i) O)=0 := by
    have hiE : parity Q (applySuper (cMap Q w β i) E)=-applySuper (cMap Q w β i) E := by rw [cMap_parity, hE]
    have hiO : parity Q (applySuper (cMap Q w β i) O)=applySuper (cMap Q w β i) O := by
      rw [cMap_parity, hO]
      change -((act (cMap Q w β i)) (-O))=_
      rw [map_neg, neg_neg]
      rfl
    rw [hsInner_conj_symm, even_odd_orthogonal Q _ _ hiO hiE]
    simp
  rw [unfilteredK, qform_sum_adj_mul, ← hsum, hsSq_add_of_orthogonal E O hEO]
  have hdecomp (i : Fin N) : hsSq (applySuper (cMap Q w β i) (E+O)) =
      hsSq (applySuper (cMap Q w β i) E)+hsSq (applySuper (cMap Q w β i) O) := by
    change hsSq ((act (cMap Q w β i)) (E+O))=_
    rw [map_add]
    exact hsSq_add_of_orthogonal _ _ (hout i)
  simp_rw [hdecomp]
  rw [Finset.sum_add_distrib]
  linarith

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
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

lemma hasGap_kernelSpan_normalized (T : Super ι) (r : Mat ι) (c : ℝ)
    (hc : 0 < c) (hg : HasGap T r c) (hr : hsSq r=1) : KernelSpan T r := by
  intro X
  constructor
  · intro hX
    let a := hsInner r X
    let Y := X-a • r
    have hrr : hsInner r r=1 := by rw [hsInner_self_real, hr]; rfl
    have ho : hsInner r Y=0 := by
      change hsInner r (X-a • r)=0
      rw [hsInner_sub_right, hsInner_smul_right, hrr, mul_one]
      exact sub_self _
    have hy : applySuper T Y=0 := by
      change (act T) (X-a • r)=0
      rw [map_sub, map_smul]
      change applySuper T X-a • applySuper T r=0
      rw [hX, hg.2.2.1, smul_zero, sub_self]
    have hq : qform T Y=0 := by simp only [qform, hy, hsInner, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
    have h := hg.2.2.2 Y ho
    rw [hq] at h
    have hz : hsSq Y=0 := by nlinarith [hsSq_nonneg Y]
    have hY := (hsSq_eq_zero_iff Y).mp hz
    exact ⟨a, sub_eq_zero.mp hY⟩
  · rintro ⟨z, rfl⟩
    change (act T) (z • r)=0
    rw [map_smul]
    change z • applySuper T r=0
    rw [hg.2.2.1, smul_zero]

end SYKFastMix.FastMixing

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

end SYKFastMix.FastMixing

open SYKFastMix.FastMixing

theorem solution {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β)
    (hjac : SYKEdge.opNorm (jacobian Q w (β/2) - 1) ≤ 1/4) :
  (∀ X, hsInner (gibbsRoot (hamiltonian Q w) β) X = 0 →
    (3/4 : ℝ) * hsSq X ≤ qform (unfilteredK Q w β) X) ∧
  KernelSpan (unfilteredK Q w β) (gibbsRoot (hamiltonian Q w) β) ∧
  HasGap (unfilteredK Q w β) (gibbsRoot (hamiltonian Q w) β) (3/4) := by
  have hform := unfiltered_form_bound Q w β hβ hjac
  have hroot := (lemma_7 Q w β hβ).2.2 (gibbsRoot (hamiltonian Q w) β) |>.mpr ⟨1, by simp⟩
  have hcroot : ∀ i, applySuper (cMap Q w β i) (gibbsRoot (hamiltonian Q w) β)=0 := by
    intro i
    rw [← bMap_even_eq_cMap Q w β i _ (parity_gibbsRoot Q w β)]
    exact hroot i
  have hKroot : applySuper (unfilteredK Q w β) (gibbsRoot (hamiltonian Q w) β)=0 := by
    rw [unfilteredK, applySuper_sum_adj_mul_eq_zero_iff]
    exact hcroot
  have hherm : (unfilteredK Q w β).IsHermitian := by
    unfold unfilteredK Matrix.IsHermitian
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hgap : HasGap (unfilteredK Q w β) (gibbsRoot (hamiltonian Q w) β) (3/4) :=
    ⟨hherm, qform_sum_adj_nonneg (cMap Q w β), hKroot, hform⟩
  letI : Nonempty (SiteHilbert N) := ⟨⟨0, by positivity⟩⟩
  have hnorm := gibbsRoot_hsSq_one (hamiltonian Q w) (hamiltonian_hermitian_words Q w) β
  exact ⟨hform, hasGap_kernelSpan_normalized _ _ (3/4) (by norm_num) hgap hnorm, hgap⟩


