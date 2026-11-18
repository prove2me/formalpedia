-- Prove2me | solution 1 for SYKFastMix.FastMixing.coefficient_bounds_to_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:52:12.16404+00:00
-- url     : https://prove2.me/submissions/d1f09bb6-3847-4bdf-855e-ae58edaba6ab

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Operators
import Definitions.Def_SYKFastMix_FastMixing_Coefficients

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
set_option backward.isDefEq.respectTransparency.types false

lemma summable_norm_map_clm {𝕜 E F I : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : E →L[𝕜] F) {f : I → E} (hf : Summable (fun i ↦ ‖f i‖)) :
    Summable (fun i ↦ ‖L (f i)‖) :=
  (hf.mul_left ‖L‖).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun i ↦ L.le_opNorm (f i)

lemma hasSum_cauchy_bilinear {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    (B : E →L[𝕜] F →L[𝕜] G) {f : ℕ → E} {g : ℕ → F} {a : E} {b : F}
    (hf : HasSum f a) (hg : HasSum g b)
    (hfn : Summable (fun i ↦ ‖f i‖)) (hgn : Summable (fun i ↦ ‖g i‖)) :
    HasSum (fun n ↦ ∑ k ∈ Finset.range (n+1), B (f k) (g (n-k))) (B a b) := by
  have hn : Summable (fun ij : ℕ × ℕ ↦ ‖B (f ij.1) (g ij.2)‖) := by
    have hmaj := (hfn.mul_of_nonneg hgn (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)).mul_left ‖B‖
    apply hmaj.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    intro ij
    calc
      ‖B (f ij.1) (g ij.2)‖ ≤ ‖B (f ij.1)‖ * ‖g ij.2‖ := (B (f ij.1)).le_opNorm _
      _ ≤ (‖B‖ * ‖f ij.1‖) * ‖g ij.2‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
      _ = _ := mul_assoc _ _ _
  have hs := hn.of_norm
  have he : (∑' ij : ℕ × ℕ, B (f ij.1) (g ij.2)) = B a b := by
    rw [hs.tsum_prod]
    have hinner (i : ℕ) : (∑' j, B (f i) (g j)) = B (f i) b :=
      (hg.mapL (B (f i))).tsum_eq
    simp_rw [hinner]
    exact (hf.mapL (B.flip b)).tsum_eq
  have hprod : HasSum (fun ij : ℕ × ℕ ↦ B (f ij.1) (g ij.2)) (B a b) := he ▸ hs.hasSum
  let e : (Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n) ≃ ℕ × ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have hsig := e.hasSum_iff.mpr hprod
  have hc := hsig.sigma (fun n ↦ hasSum_fintype (fun kl : Finset.HasAntidiagonal.antidiagonal n ↦
    B (f kl.1.1) (g kl.1.2)))
  change HasSum (fun n ↦ ∑ kl : Finset.HasAntidiagonal.antidiagonal n,
    B (f kl.1.1) (g kl.1.2)) (B a b) at hc
  convert hc using 1
  funext n
  calc
    (∑ k ∈ Finset.range (n+1), B (f k) (g (n-k))) =
        ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, B (f kl.1) (g kl.2) :=
      (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l ↦ B (f k) (g l)) n).symm
    _ = _ := (Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal n)
      (fun kl : ℕ × ℕ ↦ B (f kl.1) (g kl.2))).symm


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing

lemma gammaCoefficient_hasSum {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) (i : Fin N) :
    HasSum (fun m : ℕ ↦ (s : ℂ)^m • gammaCoefficient Q w m i) (imaginary Q w s i) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
    ((-(s : ℂ)) • ad (hamiltonian Q w))).mapL (evalSuper (Q.γ i))
  have hv : evalSuper (Q.γ i) (NormedSpace.exp ((-(s : ℂ)) • ad (hamiltonian Q w))) =
      imaginary Q w s i := by
    change applySuper (mexp ((-(s : ℂ)) • ad (hamiltonian Q w))) (Q.γ i) = _
    rw [exp_ad_apply]
    simp [imaginary, neg_neg]
  rw [hv] at h
  convert h using 1
  funext m
  simp only [gammaCoefficient, smul_pow, evalSuper_apply, applySuper_smul, smul_smul]
  congr 1
  rw [neg_eq_neg_one_mul, mul_pow]
  ring

lemma gammaCoefficient_norm_summable {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) (i : Fin N) :
    Summable (fun m : ℕ ↦ ‖(s : ℂ)^m • gammaCoefficient Q w m i‖) := by
  have h := summable_norm_map_clm (evalSuper (Q.γ i))
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) ((-(s : ℂ)) • ad (hamiltonian Q w)))
  convert h using 1
  funext m
  congr 1
  simp only [gammaCoefficient, smul_pow, evalSuper_apply, applySuper_smul, smul_smul]
  congr 1
  rw [neg_eq_neg_one_mul, mul_pow]
  ring

lemma gammaCoefficient_family_norm_summable {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) :
    Summable (fun m : ℕ ↦ ‖(s : ℂ)^m • gammaCoefficient Q w m‖) := by
  have h : Summable (fun m : ℕ ↦ ∑ i : Fin N, ‖(s : ℂ)^m • gammaCoefficient Q w m i‖) :=
    summable_sum fun i hi ↦ gammaCoefficient_norm_summable Q w s i
  apply h.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro m
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))).mpr
  intro i
  exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)

def fermionLift {N : ℕ} (Q : Model N) :
    (Fin N → Mat (SiteHilbert N)) →L[ℂ] Mat (Fin N × SiteHilbert N) where
  toFun := fun F a b ↦ ((1/2 : ℂ) • anticomm (Q.γ b.1) (F a.1)) a.2 b.2
  map_add' F G := by ext a b; simp [anticomm, mul_add, add_mul, smul_add]; ring
  map_smul' z F := by ext a b; simp [anticomm, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm]; ring
  cont := by unfold anticomm; fun_prop

lemma fermionCoefficient_hasSum {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) :
    HasSum (fun m : ℕ ↦ (s : ℂ)^m • fermionCoefficient Q w m) (jacobian Q w s) := by
  have hfamily : HasSum (fun m : ℕ ↦ (s : ℂ)^m • gammaCoefficient Q w m) (imaginary Q w s) :=
    Pi.hasSum.mpr fun i ↦ gammaCoefficient_hasSum Q w s i
  have h := hfamily.mapL (fermionLift Q)
  change HasSum (fun m ↦ fermionLift Q ((s : ℂ)^m • gammaCoefficient Q w m))
    (jacobian Q w s) at h
  convert h using 1
  funext m
  exact ((fermionLift Q).map_smul ((s : ℂ)^m) (gammaCoefficient Q w m)).symm

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing

abbrev GammaPair (N : ℕ) := (Fin N → Mat (SiteHilbert N)) × (Fin N → Mat (SiteHilbert N))

def mLiftLinear {N : ℕ} (w : Disorder N) :
    GammaPair N →ₗ[ℂ] GammaPair N →ₗ[ℂ] Mat (Fin N × (SiteHilbert N × SiteHilbert N)) :=
  LinearMap.mk₂ ℂ
    (fun (F G : GammaPair N) a b ↦ mBlock w F.1 F.2 G.1 G.2 a.1 b.1 a.2 b.2)
    (by
      intro F F' G
      ext a b
      simp [mBlock, super, sub_eq_add_neg, mul_add, add_mul, Finset.sum_add_distrib]
      <;> ring)
    (by
      intro z F G
      ext a b
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, mBlock, super,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add,
        smul_smul, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply, smul_eq_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring)
    (by
      intro F G G'
      ext a b
      simp [mBlock, super, sub_eq_add_neg, mul_add, add_mul, Finset.sum_add_distrib]
      <;> ring)
    (by
      intro z F G
      ext a b
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, mBlock, super,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add,
        smul_smul, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply, smul_eq_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring)

def mLift {N : ℕ} (w : Disorder N) :
    GammaPair N →L[ℂ] GammaPair N →L[ℂ] Mat (Fin N × (SiteHilbert N × SiteHilbert N)) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp (mLiftLinear w)).toContinuousLinearMap

@[simp] lemma mLift_apply {N : ℕ} (w : Disorder N) (F G : GammaPair N)
    (a b : Fin N × (SiteHilbert N × SiteHilbert N)) :
    mLift w F G a b = mBlock w F.1 F.2 G.1 G.2 a.1 b.1 a.2 b.2 := rfl

def pairCoefficient {N : ℕ} (Q : Model N) (w : Disorder N) (m : ℕ) : GammaPair N :=
  (gammaCoefficient Q w m, fun i ↦ (-1 : ℂ)^m • gammaCoefficient Q w m i)

lemma pairCoefficient_term {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) (m : ℕ) :
    (s : ℂ)^m • pairCoefficient Q w m =
      ((s : ℂ)^m • gammaCoefficient Q w m, ((-s : ℝ) : ℂ)^m • gammaCoefficient Q w m) := by
  apply Prod.ext
  · rfl
  · funext i
    change (s : ℂ)^m • ((-1 : ℂ)^m • gammaCoefficient Q w m i) =
      ((-s : ℝ) : ℂ)^m • gammaCoefficient Q w m i
    rw [smul_smul, Complex.ofReal_neg, neg_pow]
    congr 1
    ring

lemma pairCoefficient_hasSum {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) :
    HasSum (fun m : ℕ ↦ (s : ℂ)^m • pairCoefficient Q w m)
      (imaginary Q w s, imaginary Q w (-s)) := by
  simp_rw [pairCoefficient_term]
  exact (Pi.hasSum.mpr fun i ↦ gammaCoefficient_hasSum Q w s i).prodMk
    (Pi.hasSum.mpr fun i ↦ gammaCoefficient_hasSum Q w (-s) i)

lemma pairCoefficient_norm_summable {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) :
    Summable (fun m : ℕ ↦ ‖(s : ℂ)^m • pairCoefficient Q w m‖) := by
  simp_rw [pairCoefficient_term]
  have h := (gammaCoefficient_family_norm_summable Q w s).add
    (gammaCoefficient_family_norm_summable Q w (-s))
  apply h.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro m
  exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

lemma mCoefficient_hasSum {N : ℕ} (Q : Model N) (w : Disorder N) (s : ℝ) :
    HasSum (fun m : ℕ ↦ (s : ℂ)^m • mCoefficient Q w m) (blockM Q w s) := by
  have h := hasSum_cauchy_bilinear (mLift w) (pairCoefficient_hasSum Q w s)
    (pairCoefficient_hasSum Q w s) (pairCoefficient_norm_summable Q w s)
    (pairCoefficient_norm_summable Q w s)
  change HasSum (fun m : ℕ ↦ ∑ r ∈ Finset.range (m+1),
    mLift w ((s : ℂ)^r • pairCoefficient Q w r)
      ((s : ℂ)^(m-r) • pairCoefficient Q w (m-r))) (blockM Q w s) at h
  convert h using 1
  funext m
  have hmcoef : mCoefficient Q w m = ∑ r ∈ Finset.range (m+1),
      mLift w (pairCoefficient Q w r) (pairCoefficient Q w (m-r)) := by
    ext a b
    simp only [mCoefficient, Matrix.sum_apply, mLift_apply, pairCoefficient]
  rw [hmcoef, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrm : r ≤ m := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  rw [(mLift w).map_smul, _root_.smul_apply, map_smul, smul_smul, ← pow_add, Nat.add_sub_of_le hrm]

end SYKFastMix.FastMixing


noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SYKFastMix.FastMixing

lemma norm_series_geometric_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : ℕ → E) (a : E) (s c : ℝ) (hc : 0 ≤ c) (hsc : c * |s| < 1)
    (hF : ∀ m : ℕ, 1 ≤ m → ‖F m‖ ≤ c^m)
    (hsum : HasSum (fun m : ℕ ↦ (s : ℂ)^m • F m) a) :
    ‖a - F 0‖ ≤ c * |s| / (1 - c * |s|) := by
  have htail : HasSum (fun m : ℕ ↦ (s : ℂ)^(m+1) • F (m+1)) (a - F 0) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hsum
  have hgeo : HasSum (fun m : ℕ ↦ (c * |s|)^(m+1))
      (c * |s| / (1 - c * |s|)) := by
    convert! (hasSum_geometric_of_lt_one (mul_nonneg hc (abs_nonneg s)) hsc).mul_left
      (c * |s|) using 1
    · funext m
      rw [pow_succ']
  apply htail.norm_le_of_bounded hgeo
  intro m
  rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc
    |s|^(m+1) * ‖F (m+1)‖ ≤ |s|^(m+1) * c^(m+1) :=
      mul_le_mul_of_nonneg_left (hF (m+1) (by omega)) (by positivity)
    _ = (c * |s|)^(m+1) := by rw [mul_pow]; ring

lemma norm_series_geometric_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : ℕ → E) (a : E) (s c : ℝ) (hc : 0 ≤ c) (hsc : c * |s| < 1)
    (hF : ∀ m : ℕ, ‖F m‖ ≤ (m+1) * c^(m+1))
    (hsum : HasSum (fun m : ℕ ↦ (s : ℂ)^m • F m) a) :
    ‖a‖ ≤ c / (1 - c * |s|)^2 := by
  have hn : ‖c * |s|‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hgeo : HasSum (fun m : ℕ ↦ c * ((m+1) * (c * |s|)^m))
      (c / (1 - c * |s|)^2) := by
    convert! (hasSum_choose_mul_geometric_of_norm_lt_one 1 hn).mul_left c using 1
    · funext m
      simp
    · ring
  apply hsum.norm_le_of_bounded hgeo
  intro m
  rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc
    |s|^m * ‖F m‖ ≤ |s|^m * ((m+1) * c^(m+1)) :=
      mul_le_mul_of_nonneg_left (hF m) (by positivity)
    _ = c * ((m+1) * (c * |s|)^m) := by rw [mul_pow, pow_succ]; ring

lemma fermionCoefficient_zero {N : ℕ} (Q : Model N) (w : Disorder N) :
    fermionCoefficient Q w 0 = 1 := by
  ext a b
  simp only [fermionCoefficient, gammaCoefficient, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, one_smul]
  have hz (i : Fin N) : applySuper (1 : Super (SiteHilbert N)) (Q.γ i) = Q.γ i := by
    ext j k
    simp [applySuper, Matrix.one_apply]
  rw [hz]
  by_cases hij : a.1 = b.1
  · rw [hij]
    have hab : a = b ↔ a.2 = b.2 := by
      constructor
      · exact congrArg Prod.snd
      · intro h; exact Prod.ext hij h
    simp [anticomm, Q.car.sq, Matrix.one_apply, hab]
    split_ifs <;> norm_num
  · have hcar := Q.car.anticomm b.1 a.1 (Ne.symm hij)
    have hab : a ≠ b := fun h ↦ hij (congrArg Prod.fst h)
    simp [anticomm, hcar, Matrix.one_apply, hab]

end SYKFastMix.FastMixing

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
open SYKFastMix.FastMixing

theorem solution {N : ℕ} (Q : Model N) (w : Disorder N)
    (hF : ∀ m : ℕ, 1 ≤ m → SYKEdge.opNorm (fermionCoefficient Q w m) ≤ (133 * Q.J)^m)
    (hM : ∀ m : ℕ, SYKEdge.opNorm (mCoefficient Q w m) ≤ (m+1) * (133 * Q.J)^(m+1)) :
    ∀ s : ℝ, 133 * Q.J * |s| < 1 →
      SYKEdge.opNorm (jacobian Q w s - 1) ≤ 133 * Q.J * |s| / (1 - 133 * Q.J * |s|) ∧
      SYKEdge.opNorm (blockM Q w s) ≤ 133 * Q.J / (1 - 133 * Q.J * |s|)^2 ∧
      HasSum (fun m : ℕ => (s : ℂ)^m • fermionCoefficient Q w m) (jacobian Q w s) ∧
      HasSum (fun m : ℕ => (s : ℂ)^m • mCoefficient Q w m) (blockM Q w s) := by
  intro s hs
  have hc : 0 ≤ 133 * Q.J := mul_nonneg (by norm_num) Q.positive.le
  have hfs := fermionCoefficient_hasSum Q w s
  have hms := mCoefficient_hasSum Q w s
  refine ⟨?_, ?_, hfs, hms⟩
  · have h := norm_series_geometric_tail (fermionCoefficient Q w) (jacobian Q w s)
      s (133 * Q.J) hc hs hF hfs
    rw [fermionCoefficient_zero] at h
    exact h
  · exact norm_series_geometric_derivative (mCoefficient Q w) (blockM Q w s)
      s (133 * Q.J) hc hs hM hms



