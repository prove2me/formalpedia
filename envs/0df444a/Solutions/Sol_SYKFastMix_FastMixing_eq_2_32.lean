-- Prove2me | solution 1 for SYKFastMix.FastMixing.eq_2_32
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:31:59.689554+00:00
-- url     : https://prove2.me/submissions/7166b6d4-7372-48b1-8419-a9b1ca680d32

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
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate ComplexOrder
open SYKFastMix.FastMixing
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma gibbs_projection_kernel (H : Mat ι) (hH : H.IsHermitian) (β : ℝ) (T : Super ι)
    (hk : applySuper T (gibbsRoot H β)=0) :
    let Z := (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re
    let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
    applySuper T ((Z⁻¹ : ℂ) • R)=0 := by
  dsimp only
  let Z := (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re
  let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
  have hZ : 0 < Z := mexp_trace_pos H hH (-β)
  have hroot : gibbsRoot H β = ((Real.sqrt Z : ℂ))⁻¹ • R := by
    simp only [gibbsRoot, Z, R, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [hroot] at hk
  have hsqrt : ((Real.sqrt Z : ℂ))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (Real.sqrt_pos.mpr hZ).ne'
  change (act T) (((Real.sqrt Z : ℂ))⁻¹ • R)=0 at hk
  rw [map_smul] at hk
  have hR := (smul_eq_zero.mp hk).resolve_left hsqrt
  change (act T) ((Z⁻¹ : ℂ) • R)=0
  rw [map_smul, hR, smul_zero]

theorem solution {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (hH : H.IsHermitian)
    (hγ : ∀ i, (γ i).IsHermitian) (β rate : ℝ) (hβ : 0 ≤ β) (hrate : 0 < rate)
    (hgap : HasGap (discriminant H γ β) (gibbsRoot H β) rate) :
  ∀ τ : ℝ, 0 ≤ τ → ∀ X, IsDensity X →
    traceNorm (evolve (lindblad H γ β) τ X - gibbs H β) ≤
      Real.exp (-rate * τ) * Real.sqrt (Fintype.card ι : ℝ) * Real.exp (β * SYKEdge.opNorm H) := by
  intro t ht X hX
  let D := discriminant H γ β
  let Z := (Matrix.trace (mexp (((-β : ℝ) : ℂ) • H))).re
  let R := mexp (((-(β/2) : ℝ) : ℂ) • H)
  let C := mexp (((-(β/4) : ℝ) : ℂ) • H)
  let B := mexp (((β/4 : ℝ) : ℂ) • H)
  let W := B*X*B
  let P := (Z⁻¹ : ℂ) • R
  let V := W-P
  let E := mexp (((-t : ℝ) : ℂ) • D)
  have hP : applySuper D P=0 := gibbs_projection_kernel H hH β D hgap.2.2.1
  have hfix : applySuper E P=P := hermitian_exp_fixed D hgap.1 P hP (((-t : ℝ) : ℂ))
  have hcong : C*P*C=gibbs H β := gibbs_congruence_identity H hH β
  have hevo : evolve (lindblad H γ β) t X = C*applySuper E W*C :=
    evolve_discriminant_similarity H γ β t X
  have hmap : applySuper E V = applySuper E W-P := by
    change (act E) (W-P) = _
    rw [map_sub]
    change applySuper E W-applySuper E P = _
    rw [hfix]
  have hdiff : evolve (lindblad H γ β) t X-gibbs H β = C*applySuper E V*C := by
    rw [hevo, ← hcong, hmap, mul_sub, sub_mul]
  have hweight : hsInner (gibbsRoot H β) V=0 ∧ hs V ≤ Real.exp (β*‖H‖/2) :=
    weighted_density_projection H hH β hβ X hX
  have hdecay : hs (applySuper E V) ≤ Real.exp (-rate*t) * Real.exp (β*‖H‖/2) :=
    (hasGap_hs_decay D (gibbsRoot H β) V rate t hrate ht hgap hweight.1).trans
      (mul_le_mul_of_nonneg_left hweight.2 (Real.exp_pos _).le)
  have hC : ‖C‖ ≤ Real.exp (β*‖H‖/4) := by
    calc
      _ ≤ Real.exp (|-(β/4)| * ‖H‖) := mexp_smul_norm_le H (-(β/4))
      _ = _ := by rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ β/4)]; congr 1 <;> ring
  have hhs : hs (C*applySuper E V*C) ≤ ‖C‖*hs (applySuper E V)*‖C‖ :=
    (hs_mul_right_le (C*applySuper E V) C).trans
      (mul_le_mul_of_nonneg_right (hs_mul_left_le C (applySuper E V)) (norm_nonneg C))
  rw [hdiff]
  calc
    _ ≤ Real.sqrt (Fintype.card ι : ℝ) * hs (C*applySuper E V*C) := traceNorm_le_sqrt_card_mul_hs _
    _ ≤ Real.sqrt (Fintype.card ι : ℝ) * (‖C‖*hs (applySuper E V)*‖C‖) := by gcongr
    _ ≤ Real.sqrt (Fintype.card ι : ℝ) *
        (Real.exp (β*‖H‖/4) * (Real.exp (-rate*t)*Real.exp (β*‖H‖/2)) * Real.exp (β*‖H‖/4)) := by
      gcongr
      exact Real.sqrt_nonneg _
    _ = Real.exp (-rate*t) * Real.sqrt (Fintype.card ι : ℝ) * Real.exp (β*‖H‖) := by
      have he : Real.exp (β*‖H‖/4) * Real.exp (β*‖H‖/2) * Real.exp (β*‖H‖/4) = Real.exp (β*‖H‖) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1 <;> ring
      calc
        _ = Real.exp (-rate*t) * Real.sqrt (Fintype.card ι : ℝ) *
            (Real.exp (β*‖H‖/4) * Real.exp (β*‖H‖/2) * Real.exp (β*‖H‖/4)) := by ring
        _ = _ := by rw [he]



