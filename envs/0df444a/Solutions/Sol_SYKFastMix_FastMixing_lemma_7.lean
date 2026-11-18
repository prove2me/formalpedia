-- Prove2me | solution 1 for SYKFastMix.FastMixing.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:55:22.31602+00:00
-- url     : https://prove2.me/submissions/57a4911e-a1f5-47a5-a7cb-40d665e0950f

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Operators
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_Model

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
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
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

lemma neg_one_pow_mod_two_injective (a b : ℕ) (h : (-1 : ℂ)^a=(-1 : ℂ)^b) :
    a%2=b%2 := by
  have he : Even a ↔ Even b := by
    by_cases ha : Even a <;> by_cases hb : Even b
    · exact iff_of_true ha hb
    · norm_num [neg_one_pow_eq_ite, ha, hb] at h
    · norm_num [neg_one_pow_eq_ite, ha, hb] at h
    · exact iff_of_false ha hb
  simp only [Nat.even_iff] at he
  omega

lemma rawString_characters_injective {N : ℕ} (hN : Even N) (S T : Finset (Fin N))
    (hchar : ∀ j, (-1 : ℂ)^((S.erase j).card)=(-1 : ℂ)^((T.erase j).card)) : S=T := by
  have hm (j : Fin N) : ((S.erase j).card)%2=((T.erase j).card)%2 :=
    neg_one_pow_mod_two_injective _ _ (hchar j)
  have hpar : S.card%2=T.card%2 := by
    by_contra hp
    have hcomp (j : Fin N) : j ∈ T ↔ j ∉ S := by
      have he := hm j
      rw [Finset.card_erase_eq_ite, Finset.card_erase_eq_ite] at he
      by_cases hs : j ∈ S <;> by_cases ht : j ∈ T
      · have hsp : 1 ≤ S.card := Finset.one_le_card.mpr ⟨j, hs⟩
        have htp : 1 ≤ T.card := Finset.one_le_card.mpr ⟨j, ht⟩
        simp only [if_pos hs, if_pos ht] at he
        omega
      · simp [hs, ht]
      · simp [hs, ht]
      · simp only [if_neg hs, if_neg ht] at he
        omega
    have hd : Disjoint S T := Finset.disjoint_left.mpr fun j hs ht ↦ (hcomp j).mp ht hs
    have hu : S ∪ T=Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_cases hs : j ∈ S
      · exact Or.inl hs
      · exact Or.inr ((hcomp j).mpr hs)
    have hsum : S.card+T.card=N := by
      rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ, Fintype.card_fin]
    have heven := Nat.even_iff.mp hN
    omega
  ext j
  have he := hm j
  rw [Finset.card_erase_eq_ite, Finset.card_erase_eq_ite] at he
  by_cases hs : j ∈ S <;> by_cases ht : j ∈ T
  · simp [hs, ht]
  · have hsp : 1 ≤ S.card := Finset.one_le_card.mpr ⟨j, hs⟩
    simp only [if_pos hs, if_neg ht] at he
    omega
  · have htp : 1 ≤ T.card := Finset.one_le_card.mpr ⟨j, ht⟩
    simp only [if_neg hs, if_pos ht] at he
    omega
  · simp [hs, ht]

lemma rawString_orthogonal {N : ℕ} (Q : Model N) (S T : Finset (Fin N)) (hST : S ≠ T) :
    hsInner (rawString Q S) (rawString Q T)=0 := by
  obtain ⟨j, hj⟩ : ∃ j, (-1 : ℂ)^((S.erase j).card) ≠ (-1 : ℂ)^((T.erase j).card) := by
    by_contra h
    push_neg at h
    exact hST (rawString_characters_injective Q.even S T h)
  have hsign : (-1 : ℂ)^((S.erase j).card) * (-1 : ℂ)^((T.erase j).card) = -1 := by
    rcases neg_one_pow_eq_or ℂ ((S.erase j).card) with hS | hS <;>
      rcases neg_one_pow_eq_or ℂ ((T.erase j).card) with hT | hT <;> simp_all
  have hSc : Q.γ j * (rawString Q S)ᴴ * Q.γ j =
      (-1 : ℂ)^((S.erase j).card) • (rawString Q S)ᴴ := by
    have h := congrArg Matrix.conjTranspose (rawString_character Q S j)
    simpa only [Matrix.conjTranspose_mul, (Q.car.herm j).eq, Matrix.conjTranspose_smul,
      star_pow, star_neg, star_one, mul_assoc] using h
  have hconj : Q.γ j * ((rawString Q S)ᴴ * rawString Q T) * Q.γ j =
      ((-1 : ℂ)^((S.erase j).card) * (-1 : ℂ)^((T.erase j).card)) •
        ((rawString Q S)ᴴ * rawString Q T) := by
    calc
      _ = (Q.γ j * (rawString Q S)ᴴ * Q.γ j) * (Q.γ j * rawString Q T * Q.γ j) := by
        symm
        calc
          _ = (Q.γ j * (rawString Q S)ᴴ) * (Q.γ j * Q.γ j) * (rawString Q T * Q.γ j) := by noncomm_ring
          _ = _ := by rw [Q.car.sq]; noncomm_ring
      _ = _ := by rw [hSc, rawString_character, smul_mul_assoc, mul_smul_comm, smul_smul]
  have htrace := congrArg Matrix.trace hconj
  rw [Matrix.trace_mul_cycle, Q.car.sq, one_mul, Matrix.trace_smul, hsign] at htrace
  rw [neg_one_smul] at htrace
  unfold hsInner
  linear_combination (1/2 : ℂ) * htrace

lemma rawString_hsInner_self {N : ℕ} (Q : Model N) (S : Finset (Fin N)) :
    hsInner (rawString Q S) (rawString Q S) = (2^(N/2) : ℂ) := by
  have h := Unitary.star_mul_self_of_mem (rawString_unitary_word Q S)
  change (rawString Q S)ᴴ * rawString Q S=1 at h
  rw [hsInner, h]
  simp [SiteHilbert]

def hsInnerLinear {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) : Mat ι →ₗ[ℂ] ℂ where
  toFun := hsInner X
  map_add' Y Z := by simp [hsInner, mul_add]
  map_smul' z Y := by rw [hsInner_smul_right]; rfl

lemma rawString_linearIndependent {N : ℕ} (Q : Model N) :
    LinearIndependent ℂ (rawString Q) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc T
  have h := congrArg (hsInnerLinear (rawString Q T)) hc
  simp only [map_sum, map_smul, map_zero, hsInnerLinear, LinearMap.coe_mk, AddHom.coe_mk,
    smul_eq_mul] at h
  have he : (∑ S : Finset (Fin N), c S * hsInner (rawString Q T) (rawString Q S)) =
      c T * (2^(N/2) : ℂ) := by
    rw [Finset.sum_eq_single T]
    · rw [rawString_hsInner_self]
    · intro S hS hST
      rw [rawString_orthogonal Q T S (Ne.symm hST), mul_zero]
    · simp
  rw [he] at h
  exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (by norm_num))

lemma clifford_dimension {N : ℕ} (Q : Model N) :
    Fintype.card (Finset (Fin N)) = Module.finrank ℂ (Mat (SiteHilbert N)) := by
  simp only [Fintype.card_finset, Fintype.card_fin, Module.finrank_matrix, Module.finrank_self,
    mul_one, SiteHilbert, Fintype.card_fin]
  rw [← pow_add]
  congr 1
  have he := Nat.even_iff.mp Q.even
  omega

lemma rawString_span {N : ℕ} (Q : Model N) :
    Submodule.span ℂ (Set.range (rawString Q)) = ⊤ :=
  (rawString_linearIndependent Q).span_eq_top_of_card_eq_finrank' (clifford_dimension Q)

lemma majorana_commutant_scalar {N : ℕ} (Q : Model N) (X : Mat (SiteHilbert N))
    (hX : ∀ i, Commute X (Q.γ i)) : ∃ z : ℂ, X=z • (1 : Mat (SiteHilbert N)) := by
  have hraw (S : Finset (Fin N)) : Commute X (rawString Q S) := by
    apply Commute.list_prod_right
    intro Y hY
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hY
    exact hX i
  let F : Mat (SiteHilbert N) →ₗ[ℂ] Mat (SiteHilbert N) := (leftAct X-rightAct X).toLinearMap
  have hker : Submodule.span ℂ (Set.range (rawString Q)) ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro Y ⟨S, rfl⟩
    change X * rawString Q S - rawString Q S * X=0
    exact sub_eq_zero.mpr (hraw S).eq
  rw [rawString_span] at hker
  have hall (Y : Mat (SiteHilbert N)) : Commute X Y := by
    have hY : Y ∈ F.ker := hker (by trivial)
    change X*Y-Y*X=0 at hY
    exact sub_eq_zero.mp hY
  obtain ⟨z, hz⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr (fun i j ↦ (hall (Matrix.single i j 1)).symm)
  refine ⟨z, ?_⟩
  rw [← hz]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

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

lemma word_mul_anticommutant {N : ℕ} (Q : Model N) (X : Mat (SiteHilbert N))
    (hX : ∀ i, Q.γ i * X=-(X*Q.γ i)) (l : List (Fin N)) :
    (l.map Q.γ).prod * X = (-1 : ℂ)^l.length • (X*(l.map Q.γ).prod) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [mul_assoc, ih, mul_smul_comm, ← mul_assoc, hX, neg_mul]
    rw [smul_neg, pow_succ]
    simp only [mul_neg_one, neg_smul]
    rw [mul_assoc]

lemma majorana_anticommutant_parity {N : ℕ} (Q : Model N) (X : Mat (SiteHilbert N))
    (hX : ∀ i, Q.γ i * X=-(X*Q.γ i)) : parity Q X=X := by
  have h := word_mul_anticommutant Q X hX (Finset.univ.sort (· ≤ ·))
  have hr : rawString Q Finset.univ * X = X * rawString Q Finset.univ := by
    simpa only [Finset.length_sort, Finset.card_univ, Fintype.card_fin, Q.even.neg_one_pow,
      one_smul, rawString] using h
  have hc : parityMatrix Q * X = X * parityMatrix Q := by
    unfold parityMatrix
    rw [smul_mul_assoc, mul_smul_comm, hr]
  unfold parity
  rw [hc, mul_assoc, parityMatrix_sq, mul_one]

lemma canonical_clifford_kernel {N : ℕ} (Q : Model N) (Y : Mat (SiteHilbert N))
    (hY : ∀ i, Q.γ i * Y = parity Q Y * Q.γ i) : ∃ z : ℂ, Y=z • (1 : Mat (SiteHilbert N)) := by
  have hsecond (i : Fin N) : Q.γ i * parity Q Y=Y*Q.γ i := by
    have h := congrArg (parity Q) (hY i)
    rw [parity_mul, parity_gamma, parity_mul, parity_involution, parity_gamma] at h
    simp only [neg_mul, mul_neg] at h
    exact neg_injective h
  let O := Y-parity Q Y
  have hanti (i : Fin N) : Q.γ i * O=-(O*Q.γ i) := by
    dsimp only [O]
    rw [mul_sub, hY, hsecond]
    noncomm_ring
  have heven : parity Q O=O := majorana_anticommutant_parity Q O hanti
  have hodd : parity Q O=-O := by
    dsimp only [O]
    simp only [parity, mul_sub, sub_mul]
    change parity Q Y-parity Q (parity Q Y) = -(Y-parity Q Y)
    rw [parity_involution]
    abel
  have hz : O=0 := by
    ext i j
    change O i j=0
    have h := congrArg (fun A : Mat (SiteHilbert N) ↦ A i j) (heven.symm.trans hodd)
    change O i j = -O i j at h
    linear_combination (1/2 : ℂ) * h
  have hpar : Y=parity Q Y := sub_eq_zero.mp hz
  apply majorana_commutant_scalar Q Y
  intro i
  change Y*Q.γ i=Q.γ i*Y
  rw [hY, ← hpar]

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

lemma thermal_clifford_kernel_forward {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (X : Mat (SiteHilbert N)) (hX : ∀ i, applySuper (bMap Q w β i) X=0) :
    ∃ z : ℂ, X=z • gibbsRoot (hamiltonian Q w) β := by
  let H := hamiltonian Q w
  let B := mexp ((((β/4 : ℝ)) : ℂ) • H)
  let C := mexp (((-(β/4) : ℝ) : ℂ) • H)
  let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
  let Y := B*X*B
  have hBC : B*C=1 := by
    change mexp (((β/4 : ℝ) : ℂ) • H) * mexp (((-(β/4) : ℝ) : ℂ) • H)=1
    rw [mexp_smul_add]
    have he : ((β/4 : ℝ) : ℂ)+((-(β/4) : ℝ) : ℂ)=0 := by push_cast; ring
    rw [he]; simp [mexp]
  have hCB : C*B=1 := by
    change mexp (((-(β/4) : ℝ) : ℂ) • H) * mexp (((β/4 : ℝ) : ℂ) • H)=1
    rw [mexp_smul_add]
    have he : ((-(β/4) : ℝ) : ℂ)+((β/4 : ℝ) : ℂ)=0 := by push_cast; ring
    rw [he]; simp [mexp]
  have hCC : C*C=R := by
    change mexp (((-(β/4) : ℝ) : ℂ) • H) * mexp (((-(β/4) : ℝ) : ℂ) • H)=R
    rw [mexp_smul_add]
    congr 1
    congr 1
    push_cast
    ring
  have hparY : parity Q Y=B*parity Q X*B := by
    have hPB : parity Q B=B := parity_mexp Q w (((β/4 : ℝ) : ℂ))
    change parity Q (B*X*B)=_
    rw [parity_mul, parity_mul, hPB]
  have hcanonical (i : Fin N) : Q.γ i * Y=parity Q Y*Q.γ i := by
    have hz := hX i
    rw [bMap_apply] at hz
    have hsub := (smul_eq_zero.mp hz).resolve_left (by norm_num : (1/2 : ℂ) ≠ 0)
    have h := congrArg (fun A : Mat (SiteHilbert N) ↦ B*A*B) hsub
    have him : imaginary Q w (β/4) i=C*Q.γ i*B := by
      simp only [imaginary, C, B, H, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    have himstar : (imaginary Q w (β/4) i)ᴴ=B*Q.γ i*C := by
      rw [imaginary_conjTranspose]
      simp only [imaginary, C, B, H, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, neg_neg]
    rw [himstar, him] at h
    have he : B*(C*Q.γ i*B*X-parity Q X*(B*Q.γ i*C))*B = Q.γ i*Y-parity Q Y*Q.γ i := by
      rw [hparY]
      calc
        _ = (B*C)*Q.γ i*(B*X*B) - (B*parity Q X*B)*Q.γ i*(C*B) := by noncomm_ring
        _ = _ := by rw [hBC, hCB, one_mul, mul_one]
    rw [he] at h
    simp only [mul_zero, zero_mul] at h
    exact sub_eq_zero.mp h
  obtain ⟨z, hz⟩ := canonical_clifford_kernel Q Y hcanonical
  have hrep : X=C*Y*C := by
    calc
      _ = (C*B)*X*(B*C) := by rw [hCB, hBC, one_mul, mul_one]
      _ = _ := by dsimp only [Y]; noncomm_ring
  have hXR : X=z • R := by rw [hrep, hz, mul_smul_comm, smul_mul_assoc, mul_one, hCC]
  let Z := (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re
  have hZ : 0 < Z := mexp_trace_pos H (hamiltonian_hermitian_words Q w) (-β)
  have hsqrt : (Real.sqrt Z : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hZ).ne'
  refine ⟨z*(Real.sqrt Z : ℂ), ?_⟩
  have hr : gibbsRoot H β = ((Real.sqrt Z : ℂ))⁻¹ • R := by
    simp only [gibbsRoot, Z, R, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  change X=_ • gibbsRoot H β
  rw [hr, smul_smul, mul_assoc, mul_inv_cancel₀ hsqrt, mul_one]
  exact hXR

lemma bMap_gibbsRoot_zero {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (i : Fin N) :
    applySuper (bMap Q w β i) (gibbsRoot (hamiltonian Q w) β)=0 := by
  let H := hamiltonian Q w
  let B := mexp (((β/4 : ℝ) : ℂ) • H)
  let C := mexp (((-(β/4) : ℝ) : ℂ) • H)
  let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
  have hBR : B*R=C := by
    change mexp (((β/4 : ℝ) : ℂ) • H) * mexp (((-(β/2) : ℝ) : ℂ) • H)=C
    rw [mexp_smul_add]
    congr 1
    congr 1
    push_cast
    ring
  have hRB : R*B=C := by
    change mexp (((-(β/2) : ℝ) : ℂ) • H) * mexp (((β/4 : ℝ) : ℂ) • H)=C
    rw [mexp_smul_add]
    congr 1
    congr 1
    push_cast
    ring
  have hR0 : applySuper (bMap Q w β i) R=0 := by
    rw [bMap_apply]
    have him : imaginary Q w (β/4) i=C*Q.γ i*B := by
      simp only [imaginary, C, B, H, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    have himstar : (imaginary Q w (β/4) i)ᴴ=B*Q.γ i*C := by
      rw [imaginary_conjTranspose]
      simp only [imaginary, C, B, H, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, neg_neg]
    have hpR : parity Q R=R := parity_mexp Q w _
    rw [himstar, him, hpR]
    have he : C*Q.γ i*B*R-R*(B*Q.γ i*C)=0 := by
      calc
        _ = C*Q.γ i*(B*R)-(R*B)*Q.γ i*C := by noncomm_ring
        _ = 0 := by rw [hBR, hRB]; noncomm_ring
    rw [he, smul_zero]
  let Z := (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re
  have hr : gibbsRoot H β = ((Real.sqrt Z : ℂ))⁻¹ • R := by
    simp only [gibbsRoot, Z, R, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  change (act (bMap Q w β i)) (gibbsRoot H β)=0
  rw [hr, map_smul]
  change _ • applySuper (bMap Q w β i) R=0
  rw [hR0, smul_zero]

lemma thermal_clifford_kernel {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (X : Mat (SiteHilbert N)) :
    (∀ i, applySuper (bMap Q w β i) X=0) ↔
      ∃ z : ℂ, X=z • gibbsRoot (hamiltonian Q w) β := by
  constructor
  · exact thermal_clifford_kernel_forward Q w β X
  · rintro ⟨z, rfl⟩ i
    change (act (bMap Q w β i)) (z • gibbsRoot (hamiltonian Q w) β)=0
    rw [map_smul]
    change z • applySuper (bMap Q w β i) (gibbsRoot (hamiltonian Q w) β)=0
    rw [bMap_gibbsRoot_zero, smul_zero]

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
namespace SYKFastMix.FastMixing

lemma imaginary_car {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) (i j : Fin N) :
    anticomm (imaginary Q w s i) (imaginary Q w s j) =
      if i=j then (2 : ℂ) • (1 : Mat (SiteHilbert N)) else 0 := by
  let H := hamiltonian Q w
  let U := mexp (((-s : ℝ) : ℂ) • H)
  let V := mexp (((s : ℝ) : ℂ) • H)
  have hUV : U*V=1 := by
    change mexp (((-s : ℝ) : ℂ) • H) * mexp (((s : ℝ) : ℂ) • H)=1
    rw [mexp_smul_add]
    have he : ((-s : ℝ) : ℂ)+(s : ℂ)=0 := by push_cast; ring
    rw [he]; simp [mexp]
  have hVU : V*U=1 := by
    change mexp (((s : ℝ) : ℂ) • H) * mexp (((-s : ℝ) : ℂ) • H)=1
    rw [mexp_smul_add]
    have he : (s : ℂ)+((-s : ℝ) : ℂ)=0 := by push_cast; ring
    rw [he]; simp [mexp]
  have him (k : Fin N) : imaginary Q w s k=U*Q.γ k*V := by
    simp only [imaginary, U, V, H, Complex.ofReal_neg]
  have hp (a b : Fin N) : imaginary Q w s a * imaginary Q w s b=U*(Q.γ a*Q.γ b)*V := by
    rw [him, him]
    calc
      _ = U*Q.γ a*(V*U)*Q.γ b*V := by noncomm_ring
      _ = _ := by rw [hVU]; noncomm_ring
  unfold anticomm
  rw [hp, hp, ← add_mul, ← mul_add]
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl, Q.car.sq]
    simp only [add_mul, mul_add, mul_one, one_mul, hUV]
    module
  · rw [if_neg hij, Q.car.anticomm i j hij, neg_add_cancel, mul_zero, zero_mul]

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

lemma bMap_adjoint_apply {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (i : Fin N)
    (Y : Mat (SiteHilbert N)) :
    applySuper (bMap Q w β i)ᴴ Y =
      (1/2 : ℂ) • ((imaginary Q w (β/4) i)ᴴ * Y + parity Q Y * imaginary Q w (β/4) i) := by
  have hAdj (X : Mat (SiteHilbert N)) :
      hsInner (applySuper (bMap Q w β i) X) Y =
        hsInner X ((1/2 : ℂ) • ((imaginary Q w (β/4) i)ᴴ * Y + parity Q Y * imaginary Q w (β/4) i)) := by
    rw [bMap_apply, hsInner_smul_left, hsInner_sub_left, hsInner_leftMul, hsInner_rightMul,
      Matrix.conjTranspose_conjTranspose, hsInner_parity, parity_mul, parity_imaginary,
      mul_neg, hsInner_neg_right, hsInner_smul_right, hsInner_add_right]
    norm_num [map_ofNat]
  let F := (1/2 : ℂ) • ((imaginary Q w (β/4) i)ᴴ * Y + parity Q Y * imaginary Q w (β/4) i)
  let Z := applySuper (bMap Q w β i)ᴴ Y-F
  have hzero : hsInner Z Z=0 := by
    change hsInner Z (applySuper (bMap Q w β i)ᴴ Y-F)=0
    rw [hsInner_sub_right, ← hsInner_applySuper_adjoint, hAdj]
    exact sub_self _
  have hz : Z=0 := (hsSq_eq_zero_iff Z).mp (congrArg Complex.re hzero)
  exact sub_eq_zero.mp hz

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

lemma bMap_composition {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (i j : Fin N) (X : Mat (SiteHilbert N)) :
    applySuper (bMap Q w β i) (applySuper (bMap Q w β j) X) =
      (1/4 : ℂ) •
        (imaginary Q w (β/4) i * imaginary Q w (β/4) j * X -
         imaginary Q w (β/4) i * parity Q X * imaginary Q w (-(β/4)) j +
         imaginary Q w (β/4) j * parity Q X * imaginary Q w (-(β/4)) i -
         X * imaginary Q w (-(β/4)) j * imaginary Q w (-(β/4)) i) := by
  simp only [bMap_apply, imaginary_conjTranspose, parity_smul, parity_sub, parity_mul,
    parity_imaginary, parity_involution, neg_mul, mul_neg, neg_neg]
  simp only [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_smul]
  norm_num
  noncomm_ring

lemma bMap_anticomm {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (i j : Fin N) :
    bMap Q w β i * bMap Q w β j + bMap Q w β j * bMap Q w β i=0 := by
  apply applySuper_ext
  intro X
  rw [applySuper_add, applySuper_mul, applySuper_mul, bMap_composition, bMap_composition]
  have he :
      (imaginary Q w (β/4) i * imaginary Q w (β/4) j * X -
         imaginary Q w (β/4) i * parity Q X * imaginary Q w (-(β/4)) j +
         imaginary Q w (β/4) j * parity Q X * imaginary Q w (-(β/4)) i -
         X * imaginary Q w (-(β/4)) j * imaginary Q w (-(β/4)) i) +
      (imaginary Q w (β/4) j * imaginary Q w (β/4) i * X -
         imaginary Q w (β/4) j * parity Q X * imaginary Q w (-(β/4)) i +
         imaginary Q w (β/4) i * parity Q X * imaginary Q w (-(β/4)) j -
         X * imaginary Q w (-(β/4)) i * imaginary Q w (-(β/4)) j) =
      anticomm (imaginary Q w (β/4) i) (imaginary Q w (β/4) j) * X -
        X * anticomm (imaginary Q w (-(β/4)) j) (imaginary Q w (-(β/4)) i) := by
    unfold anticomm
    noncomm_ring
  rw [← smul_add, he, imaginary_car, imaginary_car]
  by_cases hij : i=j
  · subst j
    simp [applySuper, mul_smul_comm, smul_mul_assoc]
  · simp [hij, Ne.symm hij, applySuper]

lemma bMap_mixed_anticomm {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ)
    (i j : Fin N) (X : Mat (SiteHilbert N)) :
    applySuper (bMap Q w β i * (bMap Q w β j)ᴴ + (bMap Q w β j)ᴴ * bMap Q w β i) X =
      (1/4 : ℂ) •
        (anticomm (imaginary Q w (β/4) i) ((imaginary Q w (β/4) j)ᴴ) * X +
         X * anticomm (imaginary Q w (β/4) j) ((imaginary Q w (β/4) i)ᴴ)) := by
  simp only [applySuper_add, applySuper_mul, bMap_apply, bMap_adjoint_apply,
    imaginary_conjTranspose, parity_smul, parity_sub, parity_add, parity_mul,
    parity_imaginary, parity_involution, neg_mul, mul_neg, neg_neg]
  simp only [mul_smul_comm, smul_mul_assoc, ← smul_sub, ← smul_add, smul_smul]
  norm_num
  unfold anticomm
  noncomm_ring <;> module

end SYKFastMix.FastMixing

open SYKFastMix.FastMixing

theorem solution {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β) :
  (∀ i j, bMap Q w β i * bMap Q w β j + bMap Q w β j * bMap Q w β i = 0) ∧
  (∀ i j X, applySuper (bMap Q w β i * (bMap Q w β j)ᴴ + (bMap Q w β j)ᴴ * bMap Q w β i) X =
    (1 / 4 : ℂ) •
      (anticomm (imaginary Q w (β/4) i) ((imaginary Q w (β/4) j)ᴴ) * X +
       X * anticomm (imaginary Q w (β/4) j) ((imaginary Q w (β/4) i)ᴴ))) ∧
  (∀ X, (∀ i, applySuper (bMap Q w β i) X = 0) ↔
    ∃ z : ℂ, X = z • gibbsRoot (hamiltonian Q w) β) := by
  exact ⟨bMap_anticomm Q w β, bMap_mixed_anticomm Q w β, thermal_clifford_kernel Q w β⟩


