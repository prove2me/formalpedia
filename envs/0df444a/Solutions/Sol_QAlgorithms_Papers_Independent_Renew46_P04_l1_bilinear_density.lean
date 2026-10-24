-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.l1_bilinear_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T04:19:44.689104+00:00
-- url     : https://prove2.me/submissions/df113ccf-f95c-4eca-9579-761844191b62

import Theorems.Thm_Plasticity_Ext_BishopPhelps
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section
open scoped ENNReal
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

namespace X9

theorem bishopPhelpsBall {K E : Type*} [RCLike K] [NormedAddCommGroup E]
    [NormedSpace K E] [CompleteSpace E] (f : E →L[K] K) (eps : ℝ) (heps : 0 < eps) :
    ∃ g : E →L[K] K, ‖g - f‖ < eps ∧ ∃ y : E, ‖y‖ ≤ 1 ∧ ‖g y‖ = ‖g‖ := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ K E
  letI : IsScalarTower ℝ K E := ⟨fun r k x => by
    change (r • k) • x = (algebraMap ℝ K r) • (k • x)
    simp only [Algebra.smul_def, mul_smul]⟩
  let I := StrongDual.extendRCLikeₗᵢ (𝕜 := K) (F := E)
  obtain ⟨g, hg, y, hy, hgy⟩ := Plasticity.Ext.BishopPhelps (I.symm f) eps heps
  refine ⟨I g, ?_, y, hy, ?_⟩
  · calc
      ‖I g - f‖ = ‖I g - I (I.symm f)‖ := by rw [I.apply_symm_apply]
      _ = ‖I (g - I.symm f)‖ := by rw [map_sub]
      _ = ‖g - I.symm f‖ := I.norm_map _
      _ < eps := hg
  · apply le_antisymm
    · exact ((I g).le_opNorm y).trans (mul_le_of_le_one_right (norm_nonneg _) hy)
    · calc
        ‖I g‖ = ‖g‖ := I.norm_map _
        _ = |g y| := by rw [hgy, abs_of_nonneg (norm_nonneg _)]
        _ = |RCLike.re ((I g) y)| := by
          change |g y| = |RCLike.re (g.extendRCLike y : K)|
          rw [StrongDual.re_extendRCLike_apply]
        _ ≤ ‖(I g) y‖ := RCLike.abs_re_le_norm _

end X9

open QAlgorithms.Papers.Independent.Renew46.P04
namespace X9
variable {K X Y : Type*} [RCLike K]
variable [NormedAddCommGroup X] [NormedSpace K X]
variable [NormedAddCommGroup Y] [NormedSpace K Y]

@[simp] theorem update_pair_false (x a : X) (y : Y) :
    Function.update (pair x y) false (ULift.up a) = pair a y := by
  funext b
  cases b <;> simp [Function.update, pair] <;> rfl

@[simp] theorem update_pair_true (x : X) (y b : Y) :
    Function.update (pair x y) true (ULift.up b) = pair x b := by
  funext i
  cases i <;> simp [Function.update, pair] <;> rfl

theorem form_add_left (B : Bilinear K X Y K) (x a : X) (y : Y) :
    B (pair (x + a) y) = B (pair x y) + B (pair a y) := by
  have h := B.map_update_add (pair x y) false (ULift.up x) (ULift.up a)
  change B (Function.update (pair x y) false (ULift.up (x + a))) = _ at h
  simpa only [update_pair_false] using h

theorem form_add_right (B : Bilinear K X Y K) (x : X) (y b : Y) :
    B (pair x (y + b)) = B (pair x y) + B (pair x b) := by
  have h := B.map_update_add (pair x y) true (ULift.up y) (ULift.up b)
  change B (Function.update (pair x y) true (ULift.up (y + b))) = _ at h
  simpa only [update_pair_true] using h

theorem form_smul_left (B : Bilinear K X Y K) (c : K) (x : X) (y : Y) :
    B (pair (c • x) y) = c • B (pair x y) := by
  have h := B.map_update_smul (pair x y) false c (ULift.up x)
  change B (Function.update (pair x y) false (ULift.up (c • x))) = _ at h
  simpa only [update_pair_false] using h

theorem form_smul_right (B : Bilinear K X Y K) (c : K) (x : X) (y : Y) :
    B (pair x (c • y)) = c • B (pair x y) := by
  have h := B.map_update_smul (pair x y) true c (ULift.up y)
  change B (Function.update (pair x y) true (ULift.up (c • y))) = _ at h
  simpa only [update_pair_true] using h

def formLinear (B : Bilinear K X Y K) : X →ₗ[K] Y →ₗ[K] K where
  toFun x :=
    { toFun := fun y => B (pair x y)
      map_add' := form_add_right B x
      map_smul' := fun c y => form_smul_right B c x y }
  map_add' x a := by ext y; exact form_add_left B x a y
  map_smul' c x := by ext y; exact form_smul_left B c x y

theorem form_bound (B : Bilinear K X Y K) (x : X) (y : Y) :
    ‖B (pair x y)‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ := by
  have h := B.le_opNorm (pair x y)
  simp only [Fintype.prod_bool] at h
  change ‖B (pair x y)‖ ≤ ‖B‖ * (‖y‖ * ‖x‖) at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

def formOperator (B : Bilinear K X Y K) : X →L[K] (Y →L[K] K) :=
  (formLinear B).mkContinuous₂ ‖B‖ (form_bound B)

@[simp] theorem formOperator_apply (B : Bilinear K X Y K) (x : X) (y : Y) :
    formOperator B x y = B (pair x y) := rfl

theorem norm_formOperator (B : Bilinear K X Y K) : ‖formOperator B‖ = ‖B‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous₂_norm_le _ (norm_nonneg _) _
  · apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
    intro m
    have hm : pair (m false).down (m true).down = m := by
      funext b
      cases b <;> rfl
    have h := (formOperator B).le_opNorm₂ (m false).down (m true).down
    rw [formOperator_apply, hm] at h
    simp only [Fintype.prod_bool]
    change ‖B m‖ ≤ ‖formOperator B‖ * (‖(m true).down‖ * ‖(m false).down‖)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h

@[simp] theorem formOperator_dualBilinear (T : X →L[K] (Y →L[K] K)) :
    formOperator (dualBilinear T) = T := by
  ext x y
  rfl

@[simp] theorem formOperator_sub (B C : Bilinear K X Y K) :
    formOperator (B - C) = formOperator B - formOperator C := by
  ext x y
  rfl

end X9

namespace X9
variable {K Y : Type*} [RCLike K]
variable [NormedAddCommGroup Y] [NormedSpace K Y]

abbrev basis (n : ℕ) : LOne K ℕ := lp.single 1 n (1 : K)

@[simp] theorem norm_basis (n : ℕ) : ‖basis (K := K) n‖ = 1 := by
  simp [basis, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]

theorem single_eq_smul_basis (x : LOne K ℕ) (n : ℕ) :
    (lp.single 1 n (x n) : LOne K ℕ) = x n • basis n := by
  ext i
  by_cases h : i = n
  · subst i; simp [basis]
  · simp [basis, lp.single_apply, Pi.single_eq_of_ne h]

theorem norm_l1 (x : LOne K ℕ) : ‖x‖ = ∑' n, ‖x n‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞)) (by norm_num) x

theorem operator_norm_le_coordinates (T : LOne K ℕ →L[K] Y)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ n, ‖T (basis n)‖ ≤ C) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hs : Summable (fun n => ‖x n‖) := by
    simpa using x.2.summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  have ht := T.hasSum (lp.hasSum_single (p := (1 : ℝ≥0∞)) (by norm_num) x)
  calc
    ‖T x‖ ≤ ∑' n, ‖x n‖ * C := by
      apply ht.norm_le_of_bounded (hs.mul_right C).hasSum
      intro n
      rw [single_eq_smul_basis, map_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (h n) (norm_nonneg _)
    _ = C * ‖x‖ := by rw [tsum_mul_right, ← norm_l1, mul_comm]


def replaceCoordinate (T : LOne K ℕ →L[K] Y) (n : ℕ) (g : Y) : LOne K ℕ →L[K] Y :=
  T + (lp.evalCLM K (fun _ : ℕ => K) 1 n).smulRight (g - T (basis n))

@[simp] theorem replaceCoordinate_apply (T : LOne K ℕ →L[K] Y) (n : ℕ) (g : Y)
    (x : LOne K ℕ) : replaceCoordinate T n g x = T x + x n • (g - T (basis n)) := rfl

@[simp] theorem replaceCoordinate_basis_self (T : LOne K ℕ →L[K] Y) (n : ℕ) (g : Y) :
    replaceCoordinate T n g (basis n) = g := by
  simp [basis, lp.single_apply_self]

@[simp] theorem replaceCoordinate_basis_ne (T : LOne K ℕ →L[K] Y) (n : ℕ) (g : Y)
    (i : ℕ) (hi : i ≠ n) : replaceCoordinate T n g (basis i) = T (basis i) := by
  simp [basis, lp.single_apply, Pi.single_eq_of_ne (Ne.symm hi)]

theorem norm_replaceCoordinate_sub (T : LOne K ℕ →L[K] Y) (n : ℕ) (g : Y) :
    ‖replaceCoordinate T n g - T‖ ≤ ‖g - T (basis n)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖T x + x n • (g - T (basis n)) - T x‖ ≤ _
  rw [add_sub_cancel_left, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞) ≠ 0) x n) (norm_nonneg _)

theorem norm_replaceCoordinate (T : LOne K ℕ →L[K] Y) (n : ℕ) (g : Y)
    (hg : ‖T‖ ≤ ‖g‖) : ‖replaceCoordinate T n g‖ = ‖g‖ := by
  apply le_antisymm
  · apply operator_norm_le_coordinates _ _ (norm_nonneg _)
    intro i
    by_cases hi : i = n
    · subst i; simp
    · rw [replaceCoordinate_basis_ne _ _ _ _ hi]
      exact (show ‖T (basis i)‖ ≤ ‖T‖ from by simpa using T.le_opNorm (basis i)).trans hg
  · have h := (replaceCoordinate T n g).le_opNorm (basis n)
    simpa using h


theorem rescale_functional {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    (g : E →L[K] K) (hg : g ≠ 0) (R : ℝ) (hR : ‖g‖ ≤ R) :
    ∃ q : E →L[K] K, ‖q‖ = R ∧ ‖q - g‖ = R - ‖g‖ ∧
      ∀ y, ‖g y‖ = ‖g‖ → ‖q y‖ = ‖q‖ := by
  have hn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hc : 0 ≤ R / ‖g‖ := div_nonneg (hn.le.trans hR) hn.le
  let c : K := ((R / ‖g‖ : ℝ) : K)
  have hcn : ‖c‖ = R / ‖g‖ := by
    change ‖((R / ‖g‖ : ℝ) : K)‖ = R / ‖g‖
    rw [RCLike.norm_ofReal, abs_of_nonneg hc]
  refine ⟨c • g, ?_, ?_, ?_⟩
  · rw [norm_smul, hcn, div_mul_cancel₀ _ (ne_of_gt hn)]
  · have he : c • g - g = (c - 1) • g := by rw [sub_smul, one_smul]
    rw [he, norm_smul]
    have hcm : ‖c - 1‖ = R / ‖g‖ - 1 := by
      change ‖((R / ‖g‖ : ℝ) : K) - 1‖ = _
      rw [← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.norm_ofReal,
        abs_of_nonneg (by rw [sub_nonneg, le_div_iff₀ hn]; simpa using hR)]
    rw [hcm]
    field_simp
  · intro y hy
    simp only [ContinuousLinearMap.smul_apply, norm_smul, hy]


theorem approximate_operator [CompleteSpace Y] [Nontrivial Y]
    (T : LOne K ℕ →L[K] (Y →L[K] K)) (hT : T ≠ 0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ S : LOne K ℕ →L[K] (Y →L[K] K), ‖S - T‖ < eps ∧
      ∃ n y, ‖y‖ = 1 ∧ ‖S (basis n) y‖ = ‖S‖ := by
  have hnorm : 0 < ‖T‖ := norm_pos_iff.mpr hT
  let d := min (eps / 8) (‖T‖ / 4)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdε : d ≤ eps / 8 := min_le_left _ _
  have hdT : d ≤ ‖T‖ / 4 := min_le_right _ _
  obtain ⟨n, hn⟩ : ∃ n, ‖T‖ - d < ‖T (basis n)‖ := by
    by_contra! h
    have := operator_norm_le_coordinates T (‖T‖ - d) (by linarith) h
    linarith
  let f := T (basis n)
  have hf : ‖f‖ ≤ ‖T‖ := by simpa [f] using T.le_opNorm (basis n)
  obtain ⟨g, hgf, y, hy, hgy⟩ := bishopPhelpsBall f d hd
  have hfg : ‖f‖ ≤ ‖g‖ + ‖g - f‖ := by
    simpa only [norm_sub_rev] using norm_le_insert' f g
  have hglo : ‖T‖ - 2 * d < ‖g‖ := by dsimp [f] at hfg; linarith
  have hgpos : 0 < ‖g‖ := by linarith
  have hghi : ‖g‖ < ‖T‖ + d := by
    have := norm_le_insert' g f
    linarith
  have hg0 : g ≠ 0 := norm_pos_iff.mp hgpos
  have hy1 : ‖y‖ = 1 := by
    apply le_antisymm hy
    have := g.le_opNorm y
    rw [hgy] at this
    nlinarith
  obtain ⟨q, hq, hqg, hqy⟩ := rescale_functional g hg0 (‖T‖ + d) hghi.le
  let S := replaceCoordinate T n q
  have hS : ‖S‖ = ‖q‖ := norm_replaceCoordinate T n q (by rw [hq]; linarith)
  refine ⟨S, ?_, n, y, hy1, ?_⟩
  · calc
      ‖S - T‖ ≤ ‖q - f‖ := norm_replaceCoordinate_sub T n q
      _ ≤ ‖q - g‖ + ‖g - f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < eps := by rw [hqg]; linarith
  · rw [hS]
    change ‖replaceCoordinate T n q (basis n) y‖ = ‖q‖
    rw [replaceCoordinate_basis_self]
    exact hqy y hgy

end X9

open Filter Set
open scoped Topology TensorProduct ENNReal
universe u v
variable {K : Type*} [RCLike K]
section SequenceResults
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

theorem solution [CompleteSpace Y] [Nontrivial Y] :
    Dense {B : Bilinear K (LOne K ℕ) Y K | BilinearAttains B} := by
  classical
  apply Metric.dense_iff.2
  intro B eps heps
  by_cases hB : B = 0
  · refine ⟨B, by simpa using heps, ?_⟩
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    rw [hB]
    exact ⟨X9.basis 0, (‖y‖⁻¹ : K) • y, X9.norm_basis 0,
      norm_smul_inv_norm hy, by simp⟩
  · let T := X9.formOperator B
    have hT : T ≠ 0 := by
      intro h
      have hn : ‖B‖ = 0 := by rw [← X9.norm_formOperator B]; change ‖T‖ = 0; rw [h]; simp
      exact hB (norm_eq_zero.mp hn)
    obtain ⟨S, hdist, n, y, hy, hSy⟩ := X9.approximate_operator T hT eps heps
    refine ⟨dualBilinear S, ?_, X9.basis n, y, X9.norm_basis n, hy, ?_⟩
    · change dist (dualBilinear S) B < eps
      rw [dist_eq_norm, ← X9.norm_formOperator, X9.formOperator_sub,
        X9.formOperator_dualBilinear]
      exact hdist
    · change ‖S (X9.basis n) y‖ = ‖dualBilinear S‖
      rw [← X9.norm_formOperator, X9.formOperator_dualBilinear]
      exact hSy

end SequenceResults
end
