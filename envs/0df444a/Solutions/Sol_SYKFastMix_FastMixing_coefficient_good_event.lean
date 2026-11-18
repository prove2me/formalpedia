-- Prove2me | solution 1 for SYKFastMix.FastMixing.coefficient_good_event
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:09:54.784462+00:00
-- url     : https://prove2.me/submissions/b116049a-f9be-4b7b-9bd0-fa0d81ace8f6

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Operators
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Theorems.Thm_SYKFastMix_FastMixing_traceMoment_opNorm_bounds
import Theorems.Thm_SYKFastMix_FastMixing_corollary_11
import Theorems.Thm_SYKFastMix_FastMixing_corollary_13
import Theorems.Thm_SYKFastMix_FastMixing_fact_14

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
open scoped Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing

variable {Ω : Type} [TopologicalSpace Ω]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[fun_prop] lemma continuous_applySuper (T : Ω → Super ι) (X : Ω → Mat ι)
    (hT : Continuous T) (hX : Continuous X) :
    Continuous (fun w ↦ applySuper (T w) (X w)) := by
  unfold applySuper
  fun_prop

@[fun_prop] lemma continuous_ad : Continuous (ad : Mat ι → Super ι) := by
  unfold ad super
  fun_prop

@[fun_prop] lemma continuous_hamiltonian {N : ℕ} (Q : Model N) :
    Continuous (hamiltonian Q) := by
  unfold hamiltonian
  fun_prop

@[fun_prop] lemma continuous_gammaCoefficient {N : ℕ} (Q : Model N) (m : ℕ) (i : Fin N) :
    Continuous (fun w ↦ gammaCoefficient Q w m i) := by
  unfold gammaCoefficient
  fun_prop

@[fun_prop] lemma continuous_fermionCoefficient {N : ℕ} (Q : Model N) (m : ℕ) :
    Continuous (fun w ↦ fermionCoefficient Q w m) := by
  unfold fermionCoefficient anticomm
  fun_prop

@[fun_prop] lemma continuous_coupling {N : ℕ} (i j k l : Fin N) :
    Continuous (fun w : Disorder N ↦ coupling w i j k l) := by
  unfold coupling
  split_ifs <;> fun_prop

@[fun_prop] lemma continuous_mCoefficient {N : ℕ} (Q : Model N) (m : ℕ) :
    Continuous (fun w ↦ mCoefficient Q w m) := by
  unfold mCoefficient mBlock super
  fun_prop

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace SYKFastMix.FastMixing

lemma traceMoment_one_eq_sum_norm_sq {ι : Type} [Fintype ι] [DecidableEq ι] (A : Mat ι) :
    traceMoment 1 A = ∑ i, ∑ j, ‖A j i‖^2 := by
  simp only [traceMoment, pow_one, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (conj (A j i) * A j i).re = _
  rw [← Complex.normSq_eq_conj_mul_self]
  simp [Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma norm_matrix_le_card_mul_entry_bound {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Mat ι) (c : ℝ) (hc : 0 ≤ c) (hA : ∀ i j, ‖A i j‖ ≤ c) :
    ‖A‖ ≤ (Fintype.card ι : ℝ) * c := by
  have h := (traceMoment_opNorm_bounds 1 A).1
  change ‖A‖^2 ≤ traceMoment 1 A at h
  have ht : traceMoment 1 A ≤ ((Fintype.card ι : ℝ) * c)^2 := by
    rw [traceMoment_one_eq_sum_norm_sq]
    calc
      (∑ i, ∑ j, ‖A j i‖^2) ≤ ∑ _i : ι, ∑ _j : ι, c^2 := by
        gcongr with i j
        exact hA j i
      _ = _ := by simp; ring
  have hpos : 0 ≤ (Fintype.card ι : ℝ) * c := by positivity
  nlinarith [norm_nonneg A]

lemma norm_matrix_single_le_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) : ‖(Matrix.single i j 1 : Mat ι)‖ ≤ 1 := by
  letI : Nonempty ι := ⟨i⟩
  have h := (traceMoment_opNorm_bounds 1 (Matrix.single i j (1 : ℂ))).1
  rw [traceMoment_one_eq_sum_norm_sq] at h
  simp only [Nat.mul_one] at h
  have ht : (∑ x, ∑ y, ‖(Matrix.single i j (1 : ℂ)) y x‖^2) = (1 : ℝ) := by
    simp [Matrix.single_apply, ite_and, apply_ite, eq_comm]
  rw [ht] at h
  change ‖(Matrix.single i j 1 : Mat ι)‖^2 ≤ 1 at h
  nlinarith [norm_nonneg (Matrix.single i j (1 : ℂ))]

lemma matrix_entry_norm_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Mat ι) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let x : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j 1)
  have h := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A).le_opNorm x
  have he := PiLp.norm_apply_le ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) x) i
  have hx : ‖x‖ = 1 := by simp [x, PiLp.norm_single]
  rw [hx, mul_one] at h
  change _ ≤ ‖A‖ at h
  apply le_trans ?_ h
  convert! he using 1
  simp [x, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single]

lemma majorana_norm_le_one {N : ℕ} (Q : Model N) (i : Fin N) : ‖Q.γ i‖ ≤ 1 := by
  letI : Nonempty (SiteHilbert N) := ⟨⟨0, by positivity⟩⟩
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (Q.γ i)
  rw [(Q.car.herm i).eq, Q.car.sq, norm_one] at h
  nlinarith [norm_nonneg (Q.γ i)]

lemma ad_power_apply_norm_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (H X : Mat ι) (m : ℕ) :
    ‖applySuper ((ad H)^m) X‖ ≤ (2 * ‖H‖)^m * ‖X‖ := by
  induction m with
  | zero =>
    have he : applySuper (1 : Super ι) X = X := by ext i j; simp [applySuper, Matrix.one_apply]
    simp [he]
  | succ m ih =>
    rw [pow_succ', applySuper_mul]
    have had (Y : Mat ι) : applySuper (ad H) Y = H*Y-Y*H :=
      applySuper_super (leftAct H - rightAct H).toLinearMap Y
    rw [had]
    calc
      ‖H * applySuper (ad H ^ m) X - applySuper (ad H ^ m) X * H‖ ≤
          ‖H * applySuper (ad H ^ m) X‖ + ‖applySuper (ad H ^ m) X * H‖ := norm_sub_le _ _
      _ ≤ ‖H‖ * ‖applySuper (ad H ^ m) X‖ + ‖applySuper (ad H ^ m) X‖ * ‖H‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (2 * ‖H‖)^(m+1) * ‖X‖ := by rw [pow_succ]; nlinarith [norm_nonneg H]

lemma gammaCoefficient_norm_le {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ) (i : Fin N) :
    ‖gammaCoefficient Q w m i‖ ≤ (2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ) := by
  rw [gammaCoefficient, norm_smul, norm_div, norm_pow]
  simp only [norm_neg, norm_one, one_pow, Complex.norm_natCast]
  have hf : 0 < (m.factorial : ℝ) := by positivity
  calc
    1 / (m.factorial : ℝ) * ‖applySuper (ad (hamiltonian Q w)^m) (Q.γ i)‖ ≤
        1 / (m.factorial : ℝ) * ((2*‖hamiltonian Q w‖)^m * ‖Q.γ i‖) := by
      gcongr
      exact ad_power_apply_norm_le _ _ _
    _ ≤ (2*‖hamiltonian Q w‖)^m / (m.factorial : ℝ) := by
      calc
        _ ≤ 1 / (m.factorial : ℝ) * ((2*‖hamiltonian Q w‖)^m * 1) := by
          gcongr
          exact majorana_norm_le_one Q i
        _ = _ := by ring

lemma nat_pow_div_factorial_le_three_pow {N m : ℕ} (hm : N ≤ m) :
    (N : ℝ)^m / (m.factorial : ℝ) ≤ 3^m := by
  calc
    (N : ℝ)^m / (m.factorial : ℝ) ≤ Real.exp (N : ℝ) :=
      Real.pow_div_factorial_le_exp (N : ℝ) (by positivity) m
    _ = (Real.exp 1)^N := by rw [← Real.exp_nat_mul]; simp
    _ ≤ 3^N := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le N
    _ ≤ 3^m := pow_le_pow_right₀ (by norm_num) hm

lemma fermionCoefficient_norm_le {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ) :
    SYKEdge.opNorm (fermionCoefficient Q w m) ≤
      (N : ℝ) * 2^(N/2) * ((2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ)) := by
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) Q.size
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  letI : Nonempty (SiteHilbert N) := ⟨⟨0, by positivity⟩⟩
  have he (a b : Fin N × SiteHilbert N) :
      ‖fermionCoefficient Q w m a b‖ ≤ (2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ) := by
    apply le_trans (matrix_entry_norm_le _ a.2 b.2)
    rw [norm_smul]
    have hnorm : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
    rw [hnorm]
    have hsum := norm_add_le (Q.γ b.1 * gammaCoefficient Q w m a.1)
      (gammaCoefficient Q w m a.1 * Q.γ b.1)
    have h1 := norm_mul_le (Q.γ b.1) (gammaCoefficient Q w m a.1)
    have h2 := norm_mul_le (gammaCoefficient Q w m a.1) (Q.γ b.1)
    have hγ := majorana_norm_le_one Q b.1
    have hc := gammaCoefficient_norm_le Q w m a.1
    unfold anticomm
    nlinarith [norm_nonneg (gammaCoefficient Q w m a.1)]
  have h := norm_matrix_le_card_mul_entry_bound (fermionCoefficient Q w m)
    ((2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ)) (by positivity) he
  change ‖fermionCoefficient Q w m‖ ≤ _
  simpa [Fintype.card_prod, SiteHilbert, Nat.cast_mul, Nat.cast_pow, mul_assoc] using h

lemma gamma_bound_high_order {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ)
    (hm : N ≤ m) (hH : ‖hamiltonian Q w‖ ≤ 2 * Q.J * N) :
    (2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ) ≤ (12 * Q.J)^m := by
  have hJ := Q.positive
  calc
    (2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ) ≤
        (4 * Q.J * N)^m / (m.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right ?_ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) m
    _ = (4 * Q.J)^m * ((N : ℝ)^m / (m.factorial : ℝ)) := by rw [mul_pow]; ring
    _ ≤ (4 * Q.J)^m * 3^m := by
      gcongr
      exact nat_pow_div_factorial_le_three_pow hm
    _ = (12 * Q.J)^m := by rw [← mul_pow]; congr 1; ring

lemma fermionCoefficient_high_order {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ)
    (hm : N ≤ m) (hH : SYKEdge.opNorm (hamiltonian Q w) ≤ 2 * Q.J * N) :
    SYKEdge.opNorm (fermionCoefficient Q w m) ≤ (133 * Q.J)^m := by
  have hJ := Q.positive
  have hdim : (N : ℝ) * 2^(N/2) ≤ (4 : ℝ)^N := by
    have hn : (N : ℝ) ≤ 2^N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
    have hd : (2 : ℝ)^(N/2) ≤ 2^N := pow_le_pow_right₀ (by norm_num) (Nat.div_le_self N 2)
    calc
      (N : ℝ) * 2^(N/2) ≤ 2^N * 2^N := by gcongr
      _ = (4 : ℝ)^N := by rw [← mul_pow]; norm_num
  calc
    _ ≤ (N : ℝ) * 2^(N/2) * ((2 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ)) :=
      fermionCoefficient_norm_le Q w m
    _ ≤ (4 : ℝ)^N * (12 * Q.J)^m := by
      gcongr
      exact gamma_bound_high_order Q w m hm hH
    _ ≤ (4 : ℝ)^m * (12 * Q.J)^m := by
      gcongr <;> norm_num
    _ = (48 * Q.J)^m := by rw [← mul_pow]; congr 1; ring
    _ ≤ (133 * Q.J)^m := by gcongr <;> linarith

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing

lemma abs_coupling_le {N : ℕ} (w : Disorder N) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ A, |w A| ≤ W) (i j k l : Fin N) : |coupling w i j k l| ≤ W := by
  unfold coupling
  split_ifs with h
  · simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hw ⟨_, h⟩
  · simpa using hW

lemma mBlock_entry_norm_le {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : Disorder N) (W a b : ℝ) (hW : 0 ≤ W) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hw : ∀ A, |w A| ≤ W) (F B G D : Fin N → Mat ι)
    (hF : ∀ i, ‖F i‖ ≤ a) (hB : ∀ i, ‖B i‖ ≤ a)
    (hG : ∀ i, ‖G i‖ ≤ b) (hD : ∀ i, ‖D i‖ ≤ b)
    (i j : Fin N) (u v : ι × ι) :
    ‖mBlock w F B G D i j u v‖ ≤ (N : ℝ)^2 * W * a * b := by
  let X : Mat ι := Matrix.single v.1 v.2 1
  have hX : ‖X‖ ≤ 1 := norm_matrix_single_le_one _ _
  have hp (k l : Fin N) :
      ‖(coupling w i j k l : ℂ) • (F k * G l * X - F k * X * D l + X * B k * D l)‖ ≤
        W * (3 * a * b) := by
    have h1 : ‖F k * G l * X‖ ≤ a*b := by
      calc
        _ ≤ ‖F k‖ * ‖G l‖ * ‖X‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
        _ ≤ a*b*1 := by gcongr <;> first | exact hF k | exact hG l | exact hX
        _ = _ := mul_one _
    have h2 : ‖F k * X * D l‖ ≤ a*b := by
      calc
        _ ≤ ‖F k‖ * ‖X‖ * ‖D l‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
        _ ≤ a*1*b := by gcongr <;> first | exact hF k | exact hD l | exact hX
        _ = _ := by ring
    have h3 : ‖X * B k * D l‖ ≤ a*b := by
      calc
        _ ≤ ‖X‖ * ‖B k‖ * ‖D l‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
        _ ≤ 1*a*b := by gcongr <;> first | exact hB k | exact hD l | exact hX
        _ = _ := by ring
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul (abs_coupling_le w W hW hw i j k l) ?_ (norm_nonneg _) hW
    have hsum := norm_add_le (F k * G l * X - F k * X * D l) (X * B k * D l)
    have hsub := norm_sub_le (F k * G l * X) (F k * X * D l)
    nlinarith
  change ‖((1/3 : ℂ) • ∑ k, ∑ l,
    (coupling w i j k l : ℂ) • (F k * G l * X - F k * X * D l + X * B k * D l)) u.1 u.2‖ ≤ _
  apply le_trans (matrix_entry_norm_le _ u.1 u.2)
  rw [norm_smul]
  have hn : ‖(1/3 : ℂ)‖ = (1/3 : ℝ) := by norm_num
  rw [hn]
  have hs : ‖∑ k, ∑ l,
      (coupling w i j k l : ℂ) • (F k * G l * X - F k * X * D l + X * B k * D l)‖ ≤
      (N : ℝ)^2 * (W * (3*a*b)) := by
    calc
      _ ≤ ∑ k : Fin N, ∑ l : Fin N, W * (3*a*b) :=
        norm_sum_le_of_le _ fun k hk ↦ norm_sum_le_of_le _ fun l hl ↦ hp k l
      _ = _ := by simp; ring
  nlinarith

lemma scalar_exponential_convolution (x : ℝ) (m : ℕ) :
    (∑ r ∈ Finset.range (m+1), (x^r / (r.factorial : ℝ)) *
      (x^(m-r) / ((m-r).factorial : ℝ))) = (2*x)^m / (m.factorial : ℝ) := by
  calc
    _ = ∑ r ∈ Finset.range (m+1), (m.choose r : ℝ) * x^m / (m.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrm : r ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      rw [Nat.cast_choose ℝ hrm]
      have he : x^r * x^(m-r) = x^m := by rw [← pow_add, Nat.add_sub_of_le hrm]
      field_simp
      nlinarith
    _ = (2 : ℝ)^m * x^m / (m.factorial : ℝ) := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose m
    _ = _ := by rw [mul_pow]

lemma mCoefficient_norm_le {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ A, |w A| ≤ W) :
    SYKEdge.opNorm (mCoefficient Q w m) ≤
      (N : ℝ)^3 * (2^(N/2) : ℝ)^2 * W *
        ((4 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ)) := by
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) Q.size
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  letI : Nonempty (SiteHilbert N) := ⟨⟨0, by positivity⟩⟩
  let a (r : ℕ) : ℝ := (2*‖hamiltonian Q w‖)^r / (r.factorial : ℝ)
  have ha (r : ℕ) : 0 ≤ a r := by dsimp [a]; positivity
  have hc (r : ℕ) (i : Fin N) : ‖gammaCoefficient Q w r i‖ ≤ a r := gammaCoefficient_norm_le Q w r i
  have hd (r : ℕ) (i : Fin N) : ‖(-1 : ℂ)^r • gammaCoefficient Q w r i‖ ≤ a r := by
    simpa only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using hc r i
  have he (u v : Fin N × (SiteHilbert N × SiteHilbert N)) :
      ‖mCoefficient Q w m u v‖ ≤ (N : ℝ)^2 * W *
        ((4 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ)) := by
    change ‖∑ r ∈ Finset.range (m+1), _‖ ≤ _
    calc
      _ ≤ ∑ r ∈ Finset.range (m+1), (N : ℝ)^2 * W * (a r) * (a (m-r)) := by
        apply norm_sum_le_of_le
        intro r hr
        exact mBlock_entry_norm_le w W (a r) (a (m-r)) hW (ha r) (ha (m-r)) hw
          _ _ _ _ (hc r) (hd r) (hc (m-r)) (hd (m-r)) _ _ _ _
      _ = (N : ℝ)^2 * W * ∑ r ∈ Finset.range (m+1), a r * a (m-r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = _ := by
        dsimp only [a]
        rw [scalar_exponential_convolution]
        congr 3
        ring
  have h := norm_matrix_le_card_mul_entry_bound (mCoefficient Q w m)
    ((N : ℝ)^2 * W * ((4 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ))) (by positivity) he
  change ‖mCoefficient Q w m‖ ≤ _
  calc
    _ ≤ _ := h
    _ = _ := by simp [SiteHilbert, Fintype.card_prod, Nat.cast_mul, Nat.cast_pow]; ring

lemma nat_fourth_le_geometric {N : ℕ} (hN : 4 ≤ N) :
    (N : ℝ)^4 ≤ 7 * (5/2 : ℝ)^N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hstep : ((n : ℝ)+1)^4 ≤ (5/4 : ℝ)^4 * (n : ℝ)^4 := by
      rw [← mul_pow]
      gcongr
      linarith
    have hmul := mul_le_mul_of_nonneg_left ih (show 0 ≤ (5/4 : ℝ)^4 by norm_num)
    rw [Nat.cast_add, Nat.cast_one, pow_succ (5/2 : ℝ) n]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 5/2) n]

lemma mCoefficient_high_order {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ)
    (hm : N ≤ m) (hH : SYKEdge.opNorm (hamiltonian Q w) ≤ 2 * Q.J * N)
    (hw : ∀ A, |w A| ≤ 2 * Q.J * N) :
    SYKEdge.opNorm (mCoefficient Q w m) ≤ (m+1) * (133 * Q.J)^(m+1) := by
  have hJ := Q.positive
  have hf : (4 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ) ≤ (24 * Q.J)^m := by
    calc
      _ ≤ (8 * Q.J * N)^m / (m.factorial : ℝ) := by
        apply div_le_div_of_nonneg_right ?_ (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by change ‖hamiltonian Q w‖ ≤ _ at hH; linarith) m
      _ = (8*Q.J)^m * ((N : ℝ)^m / (m.factorial : ℝ)) := by rw [mul_pow]; ring
      _ ≤ (8*Q.J)^m * 3^m := by gcongr; exact nat_pow_div_factorial_le_three_pow hm
      _ = (24*Q.J)^m := by rw [← mul_pow]; congr 1; ring
  have hd : (2^(N/2) : ℝ)^2 ≤ 2^N := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.div_mul_le_self N 2)
  have hn := nat_fourth_le_geometric Q.size
  calc
    _ ≤ (N : ℝ)^3 * (2^(N/2) : ℝ)^2 * (2 * Q.J * N) *
        ((4 * ‖hamiltonian Q w‖)^m / (m.factorial : ℝ)) :=
      mCoefficient_norm_le Q w m (2*Q.J*N) (by positivity) hw
    _ ≤ 2*Q.J * (N : ℝ)^4 * (2 : ℝ)^N * (24*Q.J)^m := by
      calc
        _ ≤ (N : ℝ)^3 * (2 : ℝ)^N * (2*Q.J*N) * (24*Q.J)^m := by gcongr
        _ = _ := by ring
    _ ≤ 14*Q.J * (5 : ℝ)^N * (24*Q.J)^m := by
      calc
        _ ≤ 2*Q.J * (7*(5/2 : ℝ)^N) * (2 : ℝ)^N * (24*Q.J)^m := by gcongr
        _ = _ := by rw [show (5 : ℝ)^N = (5/2 : ℝ)^N * 2^N by rw [← mul_pow]; norm_num]; ring
    _ ≤ 14*Q.J * (5 : ℝ)^m * (24*Q.J)^m := by gcongr <;> norm_num
    _ = 14*Q.J * (120*Q.J)^m := by
      rw [mul_assoc (14*Q.J), ← mul_pow]
      congr 2
      ring
    _ ≤ 133*Q.J * (133*Q.J)^m := by gcongr <;> linarith
    _ ≤ (m+1) * (133*Q.J)^(m+1) := by
      rw [pow_succ]
      have hp : 0 ≤ (m : ℝ) * (133*Q.J * (133*Q.J)^m) := by positivity
      nlinarith

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace SYKFastMix.FastMixing

lemma disorder_coordinate_subgaussian {N : ℕ} (Q : Model N) (A : SYKEdge.KSet N 4) :
    HasSubgaussianMGF (fun w : Disorder N ↦ w A)
      (Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3)) (disorderLaw Q) := by
  let v := Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3)
  have hm : (disorderLaw Q).map (fun w ↦ w A) = gaussianReal 0 v := by
    exact (measurePreserving_eval _ A).map_eq
  refine ⟨?_, ?_⟩
  · intro t
    change Integrable (fun w : Disorder N ↦ Real.exp (t * w A))
      (Measure.pi (fun _ : SYKEdge.KSet N 4 ↦ gaussianReal 0 v))
    exact (measurePreserving_eval (fun _ : SYKEdge.KSet N 4 ↦ gaussianReal 0 v) A).integrable_comp_of_integrable
      (integrable_exp_mul_gaussianReal t)
  · intro t
    rw [mgf_gaussianReal hm]
    simp [v]

lemma disorder_coordinate_abs_tail {N : ℕ} (Q : Model N) (A : SYKEdge.KSet N 4)
    (t : ℝ) (ht : 0 ≤ t) :
    (disorderLaw Q).real {w | t < |w A|} ≤
      2 * Real.exp (-t^2 / (2 * (Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3) : ℝ))) := by
  letI : IsProbabilityMeasure (disorderLaw Q) := by unfold disorderLaw; infer_instance
  have h := disorder_coordinate_subgaussian Q A
  have hp := h.measure_ge_le ht
  have hn := h.neg.measure_ge_le ht
  calc
    _ ≤ (disorderLaw Q).real ({w | t ≤ w A} ∪ {w | t ≤ -w A}) := by
      apply measureReal_mono
      intro w hw
      change t < |w A| at hw
      rcases lt_abs.mp hw with hw | hw
      · exact Or.inl hw.le
      · exact Or.inr hw.le
      exact measure_ne_top _ _
    _ ≤ (disorderLaw Q).real {w | t ≤ w A} + (disorderLaw Q).real {w | t ≤ -w A} :=
      measureReal_union_le _ _
    _ ≤ _ := by
      change (disorderLaw Q).real {w | t ≤ -w A} ≤ _ at hn
      linarith

lemma coordinate_bad_event {N : ℕ} (Q : Model N) :
    ∃ B : Set (Disorder N), MeasurableSet B ∧
      (disorderLaw Q).real B ≤ (1/4 : ℝ)^N ∧
      ∀ w ∉ B, ∀ A, |w A| ≤ 2 * Q.J * N := by
  letI : IsProbabilityMeasure (disorderLaw Q) := by unfold disorderLaw; infer_instance
  have hJ := Q.positive
  have hN : (4 : ℝ) ≤ N := by exact_mod_cast Q.size
  have hNpos : (0 : ℝ) < N := by linarith
  have hv : 0 < 6 * Q.J^2 / (N : ℝ)^3 := by positivity
  let B : Set (Disorder N) := ⋃ A : SYKEdge.KSet N 4, {w | 2*Q.J*N < |w A|}
  have hB : MeasurableSet B := by
    apply MeasurableSet.iUnion
    intro A
    exact measurableSet_lt measurable_const (by fun_prop)
  have hcard : (Fintype.card (SYKEdge.KSet N 4) : ℝ) ≤ (N : ℝ)^4 := by
    have heq : Fintype.card (SYKEdge.KSet N 4) = N.choose 4 := by simp [SYKEdge.KSet]
    rw [heq]
    exact_mod_cast Nat.choose_le_pow N 4
  have he : -(2*Q.J*N)^2 / (2 * (Real.toNNReal (6 * Q.J^2 / (N : ℝ)^3) : ℝ)) ≤ -8*(N : ℝ) := by
    rw [Real.coe_toNNReal _ hv.le]
    have hid : -(2*Q.J*N)^2 / (2 * (6*Q.J^2/(N : ℝ)^3)) = -(N : ℝ)^5/3 := by
      field_simp
      <;> ring
    rw [hid]
    have hn4 : (4 : ℝ)^4 ≤ (N : ℝ)^4 := pow_le_pow_left₀ (by norm_num) hN 4
    have hh := mul_le_mul_of_nonneg_right hn4 hNpos.le
    nlinarith
  have hb : (disorderLaw Q).real B ≤ (1/4 : ℝ)^N := by
    calc
      _ ≤ ∑ A : SYKEdge.KSet N 4, 2*Real.exp (-8*(N : ℝ)) := by
        apply (measureReal_iUnion_fintype_le _).trans
        apply Finset.sum_le_sum
        intro A hA
        exact (disorder_coordinate_abs_tail Q A (2*Q.J*N) (by positivity)).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num))
      _ = (Fintype.card (SYKEdge.KSet N 4) : ℝ) * (2*Real.exp (-8*(N : ℝ))) := by simp
      _ ≤ (N : ℝ)^4 * (2*Real.exp (-8*(N : ℝ))) := by gcongr
      _ ≤ (7*(5/2 : ℝ)^N) * (2*Real.exp (-8*(N : ℝ))) := by
        gcongr
        exact nat_fourth_le_geometric Q.size
      _ = 14 * ((5/2 : ℝ) * (Real.exp (-1))^8)^N := by
        rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
        have harg : ((8*N : ℕ) : ℝ) * (-1) = -8*(N : ℝ) := by push_cast; ring
        rw [harg]
        ring
      _ ≤ 14 * ((5/2 : ℝ) * (1/2 : ℝ)^8)^N := by
        gcongr
        rw [Real.exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) Real.exp_one_gt_two.le
      _ ≤ (14 : ℝ)^N * ((5/2 : ℝ) * (1/2 : ℝ)^8)^N := by
        gcongr
        simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 14) (by have hs := Q.size; omega : 1 ≤ N)
      _ ≤ (1/4 : ℝ)^N := by rw [← mul_pow]; gcongr <;> norm_num
  refine ⟨B, hB, hb, ?_⟩
  intro w hw A
  by_contra h
  exact hw (Set.mem_iUnion.mpr ⟨A, lt_of_not_ge h⟩)

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace SYKFastMix.FastMixing

lemma measureReal_norm_tail_of_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (k : ℕ) (t C : ℝ)
    (ht : 0 < t) (hf : ∀ w, 0 ≤ f w) (hi : Integrable (fun w ↦ f w^k) μ)
    (hC : (∫ w, f w^k ∂μ) ≤ C) :
    μ.real {w | t < f w} ≤ C / t^k := by
  calc
    μ.real {w | t < f w} ≤ μ.real {w | t^k ≤ f w^k} := by
      apply measureReal_mono
      intro w hw
      exact pow_le_pow_left₀ ht.le hw.le k
      exact measure_ne_top μ _
    _ ≤ C / t^k := by
      apply (le_div_iff₀ (pow_pos ht k)).mpr
      rw [mul_comm]
      exact (mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall fun w ↦ pow_nonneg (hf w) k) hi (t^k)).trans hC

lemma fermion_coefficient_tail {N : ℕ} (Q : Model N) (m p : ℕ)
    (hm : 1 ≤ m) (hp : 1 ≤ p) (hmp : m*p ≤ 7*N) :
    (disorderLaw Q).real {w | (133 * Q.J)^m < SYKEdge.opNorm (fermionCoefficient Q w m)} ≤
      (N : ℝ) * 2^(N/2) * (105/133 : ℝ)^(2*p*m) := by
  letI : IsProbabilityMeasure (disorderLaw Q) := by unfold disorderLaw; infer_instance
  have hJ := Q.positive
  have h := corollary_11 Q m p hm hp hmp
  have ht := measureReal_norm_tail_of_moment (disorderLaw Q)
    (fun w ↦ SYKEdge.opNorm (fermionCoefficient Q w m)) (2*p) ((133*Q.J)^m)
    ((N : ℝ) * 2^(N/2) * (105*Q.J)^(2*p*m)) (by positivity) (fun _ ↦ norm_nonneg _)
    h.1 h.2
  convert ht using 1
  simp only [← pow_mul, mul_pow, div_pow]
  simp only [show m*(2*p) = 2*p*m by ring]
  field_simp [ne_of_gt hJ]
  <;> ring

lemma m_coefficient_tail {N : ℕ} (Q : Model N) (m p : ℕ)
    (hp : 1 ≤ p) (hmp : (m+1)*p ≤ 7*N) :
    (disorderLaw Q).real {w | (m+1) * (133 * Q.J)^(m+1) < SYKEdge.opNorm (mCoefficient Q w m)} ≤
      (N : ℝ) * (2^(N/2) : ℝ)^2 * (105/133 : ℝ)^(2*p*(m+1)) := by
  letI : IsProbabilityMeasure (disorderLaw Q) := by unfold disorderLaw; infer_instance
  have hJ := Q.positive
  have h := corollary_13 Q m p hp hmp
  have ht := measureReal_norm_tail_of_moment (disorderLaw Q)
    (fun w ↦ SYKEdge.opNorm (mCoefficient Q w m)) (2*p) ((m+1) * (133*Q.J)^(m+1))
    ((N : ℝ) * (2^(N/2) : ℝ)^2 * ((m : ℝ)+1)^(2*p) * (105*Q.J)^(2*p*(m+1)))
    (by positivity) (fun _ ↦ norm_nonneg _) h.1 h.2
  convert ht using 1
  simp only [mul_pow, ← pow_mul, div_pow]
  simp only [show (m+1)*(2*p) = 2*p*(m+1) by ring]
  field_simp [ne_of_gt hJ]
  <;> ring

lemma coefficient_moment_order {N m : ℕ} (hN : 4 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N) :
    ∃ p : ℕ, 1 ≤ p ∧ 6*N ≤ m*p ∧ m*p ≤ 7*N := by
  let p : ℕ := ⌈(6 : ℝ)*N/m⌉₊
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hp : 0 < p := Nat.ceil_pos.mpr (by positivity)
  have hlo : (6 : ℝ)*N ≤ m*p := by
    have h := Nat.le_ceil ((6 : ℝ)*N/m)
    dsimp only [p]
    exact (div_le_iff₀ hmr).mp h |>.trans_eq (mul_comm _ _)
  have hhi : (m : ℝ)*p ≤ 7*N := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (6 : ℝ)*N/m by positivity)
    change (p : ℝ) < (6 : ℝ)*N/m+1 at h
    have hmul := mul_lt_mul_of_pos_left h hmr
    have hmNr : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have heq : (m : ℝ) * ((6 : ℝ)*N/m+1) = 6*N+m := by field_simp
    rw [heq] at hmul
    linarith
  refine ⟨p, hp, ?_, ?_⟩
  · exact_mod_cast hlo
  · exact_mod_cast hhi

lemma nat_sq_le_two_pow {N : ℕ} (hN : 4 ≤ N) : (N : ℝ)^2 ≤ 2^N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Nat.cast_add, Nat.cast_one, pow_succ (2 : ℝ) n]
    have hnr : (4 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ)-2)]

lemma fermion_coefficient_low_tail {N : ℕ} (Q : Model N) (m : ℕ)
    (hm : 1 ≤ m) (hmN : m ≤ N) :
    (disorderLaw Q).real {w | (133 * Q.J)^m < SYKEdge.opNorm (fermionCoefficient Q w m)} ≤
      (N : ℝ) * 2^(N/2) * (105/133 : ℝ)^(12*N) := by
  obtain ⟨p, hp, hlo, hhi⟩ := coefficient_moment_order Q.size hm hmN
  apply (fermion_coefficient_tail Q m p hm hp hhi).trans
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  nlinarith

lemma m_coefficient_low_tail {N : ℕ} (Q : Model N) (m : ℕ) (hmN : m+1 ≤ N) :
    (disorderLaw Q).real {w | (m+1) * (133 * Q.J)^(m+1) < SYKEdge.opNorm (mCoefficient Q w m)} ≤
      (N : ℝ) * (2^(N/2) : ℝ)^2 * (105/133 : ℝ)^(12*N) := by
  obtain ⟨p, hp, hlo, hhi⟩ := coefficient_moment_order Q.size (by omega : 1 ≤ m+1) hmN
  apply (m_coefficient_tail Q m p hp hhi).trans
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  nlinarith

lemma low_coefficient_bad_event {N : ℕ} (Q : Model N) :
    ∃ B : Set (Disorder N), MeasurableSet B ∧
      (disorderLaw Q).real B ≤ 2 * (1/4 : ℝ)^N ∧
      ∀ w ∉ B,
        (∀ m : ℕ, 1 ≤ m → m ≤ N → SYKEdge.opNorm (fermionCoefficient Q w m) ≤ (133*Q.J)^m) ∧
        (∀ m : ℕ, m < N → SYKEdge.opNorm (mCoefficient Q w m) ≤ (m+1)*(133*Q.J)^(m+1)) := by
  letI : IsProbabilityMeasure (disorderLaw Q) := by unfold disorderLaw; infer_instance
  let BF : Set (Disorder N) := ⋃ m ∈ Finset.Icc 1 N,
    {w | (133*Q.J)^m < SYKEdge.opNorm (fermionCoefficient Q w m)}
  let BM : Set (Disorder N) := ⋃ m ∈ Finset.range N,
    {w | (m+1)*(133*Q.J)^(m+1) < SYKEdge.opNorm (mCoefficient Q w m)}
  have hBF : MeasurableSet BF := by
    apply MeasurableSet.iUnion
    intro m
    apply MeasurableSet.iUnion
    intro hm
    apply measurableSet_lt measurable_const
    change Measurable (fun w ↦ ‖fermionCoefficient Q w m‖)
    exact (continuous_fermionCoefficient Q m).norm.measurable
  have hBM : MeasurableSet BM := by
    apply MeasurableSet.iUnion
    intro m
    apply MeasurableSet.iUnion
    intro hm
    apply measurableSet_lt measurable_const
    change Measurable (fun w ↦ ‖mCoefficient Q w m‖)
    exact (continuous_mCoefficient Q m).norm.measurable
  have hFbound : (disorderLaw Q).real BF ≤
      (N : ℝ)^2 * 2^(N/2) * (105/133 : ℝ)^(12*N) := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 N,
          (N : ℝ) * 2^(N/2) * (105/133 : ℝ)^(12*N) := by
        apply (measureReal_biUnion_finset_le _ _).trans
        apply Finset.sum_le_sum
        intro m hm
        exact fermion_coefficient_low_tail Q m (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
      _ = _ := by simp [Nat.card_Icc]; ring
  have hMbound : (disorderLaw Q).real BM ≤
      (N : ℝ)^2 * (2^(N/2) : ℝ)^2 * (105/133 : ℝ)^(12*N) := by
    calc
      _ ≤ ∑ m ∈ Finset.range N,
          (N : ℝ) * (2^(N/2) : ℝ)^2 * (105/133 : ℝ)^(12*N) := by
        apply (measureReal_biUnion_finset_le _ _).trans
        apply Finset.sum_le_sum
        intro m hm
        exact m_coefficient_low_tail Q m (Finset.mem_range.mp hm)
      _ = _ := by simp; ring
  have hd : (2^(N/2) : ℝ) ≤ 2^N :=
    pow_le_pow_right₀ (by norm_num) (Nat.div_le_self N 2)
  have hd2 : (2^(N/2) : ℝ)^2 ≤ 2^N := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.div_mul_le_self N 2)
  have hb : (disorderLaw Q).real (BF ∪ BM) ≤ 2*(1/4 : ℝ)^N := by
    calc
      _ ≤ (disorderLaw Q).real BF + (disorderLaw Q).real BM := measureReal_union_le _ _
      _ ≤ (N : ℝ)^2 * 2^(N/2) * (105/133 : ℝ)^(12*N) +
          (N : ℝ)^2 * (2^(N/2) : ℝ)^2 * (105/133 : ℝ)^(12*N) := add_le_add hFbound hMbound
      _ ≤ (N : ℝ)^2 * (2 : ℝ)^N * (105/133 : ℝ)^(12*N) +
          (N : ℝ)^2 * (2 : ℝ)^N * (105/133 : ℝ)^(12*N) := by gcongr
      _ ≤ (2 : ℝ)^N * (2 : ℝ)^N * (105/133 : ℝ)^(12*N) +
          (2 : ℝ)^N * (2 : ℝ)^N * (105/133 : ℝ)^(12*N) := by
        gcongr <;> exact nat_sq_le_two_pow Q.size
      _ = 2 * ((4 : ℝ) * (105/133 : ℝ)^12)^N := by
        rw [mul_pow, pow_mul]
        rw [show (4 : ℝ)^N = 2^N * 2^N by rw [← mul_pow]; norm_num]
        ring
      _ ≤ 2*(1/4 : ℝ)^N := by gcongr <;> norm_num
  refine ⟨BF ∪ BM, hBF.union hBM, hb, ?_⟩
  intro w hw
  refine ⟨?_, ?_⟩
  · intro m hm hmN
    by_contra h
    apply hw
    left
    exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hm, hmN⟩, lt_of_not_ge h⟩⟩
  · intro m hmN
    by_contra h
    apply hw
    right
    exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hmN, lt_of_not_ge h⟩⟩

end SYKFastMix.FastMixing

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace SYKFastMix.FastMixing

lemma fact14_failure_le_quarter_pow {N : ℕ} (Q : Model N) :
    (disorderLaw Q).real {w | SYKEdge.opNorm (hamiltonian Q w) > 2*Q.J*N} ≤ (1/4 : ℝ)^N := by
  have h := (fact_14 Q).2
  have hn : Real.rpow 2 (-(5*(N : ℝ)/2)) ≤ (1/4 : ℝ)^N := by
    simp only [Real.rpow_eq_pow]
    calc
      _ ≤ (2 : ℝ)^((-2 : ℝ)*N) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
      _ = _ := by rw [Real.rpow_mul_natCast (by norm_num)]; norm_num
  apply le_trans ?_ hn
  have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h
  simp only [Real.rpow_eq_pow] at ht ⊢
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num) _)] at ht
  exact ht

lemma total_coefficient_failure_bound {N : ℕ} (hN : 4 ≤ N) :
    4*(1/4 : ℝ)^N ≤ 2*Real.exp (-(N : ℝ)) := by
  have he : Real.exp (N : ℝ) ≤ (3 : ℝ)^N := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le N
  have hp : (3/4 : ℝ)^N ≤ (3/4 : ℝ)^4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
  have hb : (4*(1/4 : ℝ)^N) * Real.exp (N : ℝ) ≤ 2 := by
    calc
      _ ≤ (4*(1/4 : ℝ)^N) * (3 : ℝ)^N := by gcongr
      _ = 4*(3/4 : ℝ)^N := by rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ 4*(3/4 : ℝ)^4 := by gcongr
      _ ≤ 2 := by norm_num
  have hexp := Real.exp_pos (N : ℝ)
  rw [Real.exp_neg]
  simpa only [div_eq_mul_inv] using (le_div_iff₀ hexp).mpr hb

end SYKFastMix.FastMixing

open SYKFastMix.FastMixing

theorem solution {N : ℕ} (Q : Model N) :
  ∃ A : Set (Disorder N), MeasurableSet A ∧
    ENNReal.ofReal (1 - 2 * Real.exp (-(N : ℝ))) ≤ disorderLaw Q A ∧
    ∀ w ∈ A, SYKEdge.opNorm (hamiltonian Q w) ≤ 2 * Q.J * N ∧
      (∀ m : ℕ, 1 ≤ m → SYKEdge.opNorm (fermionCoefficient Q w m) ≤ (133 * Q.J)^m) ∧
      (∀ m : ℕ, SYKEdge.opNorm (mCoefficient Q w m) ≤ (m+1) * (133 * Q.J)^(m+1)) := by
  letI : IsProbabilityMeasure (disorderLaw Q) := by unfold disorderLaw; infer_instance
  obtain ⟨B, hB, hpB, hlow⟩ := low_coefficient_bad_event Q
  obtain ⟨C, hC, hpC, hcoord⟩ := coordinate_bad_event Q
  let Hbad : Set (Disorder N) := {w | SYKEdge.opNorm (hamiltonian Q w) > 2*Q.J*N}
  have hHbad : MeasurableSet Hbad := (fact_14 Q).1
  have hpH : (disorderLaw Q).real Hbad ≤ (1/4 : ℝ)^N := fact14_failure_le_quarter_pow Q
  let bad := (B ∪ C) ∪ Hbad
  have hbad : MeasurableSet bad := (hB.union hC).union hHbad
  have hpbad : (disorderLaw Q).real bad ≤ 2*Real.exp (-(N : ℝ)) := by
    calc
      _ ≤ ((disorderLaw Q).real B + (disorderLaw Q).real C) + (disorderLaw Q).real Hbad :=
        (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le B C) le_rfl)
      _ ≤ 4*(1/4 : ℝ)^N := by linarith
      _ ≤ _ := total_coefficient_failure_bound Q.size
  refine ⟨badᶜ, hbad.compl, ?_, ?_⟩
  · rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    rw [measureReal_compl hbad, probReal_univ]
    linarith
  · intro w hw
    have hnot : w ∉ bad := hw
    have hwB : w ∉ B := fun h ↦ hnot (Or.inl (Or.inl h))
    have hwC : w ∉ C := fun h ↦ hnot (Or.inl (Or.inr h))
    have hwH : w ∉ Hbad := fun h ↦ hnot (Or.inr h)
    have hH : SYKEdge.opNorm (hamiltonian Q w) ≤ 2*Q.J*N := le_of_not_gt hwH
    obtain ⟨hF, hM⟩ := hlow w hwB
    refine ⟨hH, ?_, ?_⟩
    · intro m hm
      by_cases hmN : m ≤ N
      · exact hF m hm hmN
      · exact fermionCoefficient_high_order Q w m (by omega) hH
    · intro m
      by_cases hmN : m < N
      · exact hM m hmN
      · exact mCoefficient_high_order Q w m (by omega) hH (hcoord w hwC)


