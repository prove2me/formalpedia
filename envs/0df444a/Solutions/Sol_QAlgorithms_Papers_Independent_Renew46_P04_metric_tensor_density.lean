-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.metric_tensor_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:37:19.324499+00:00
-- url     : https://prove2.me/submissions/2d4af2e2-fb94-490c-9b7c-99a89af6d7ff

import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_projective_series
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_projective_crossnorm_ball
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_extension
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_finite_dimensional_tensors
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_finite_uniform_tensor_density
import Mathlib.Tactic

noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000

open QAlgorithms.Papers.Independent.Renew46.P04
open scoped BigOperators

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

namespace X9Metric
variable {K X Y : Type*} [RCLike K]
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

noncomputable def algebraicPair : X →ₗ[K] Y →ₗ[K] Algebraic K X Y :=
  LinearMap.mk₂ K (fun x y => PiTensorProduct.tprod K (pair x y))
    (fun x x' y => by
      have e : ∀ x0 : X, pair x0 y = Function.update (pair 0 y) false (ULift.up x0) := by
        intro x0; funext b; cases b <;> rfl
      rw [e (x + x'), e x, e x']
      exact (PiTensorProduct.tprod K).map_update_add (pair 0 y) false (ULift.up x) (ULift.up x'))
    (fun c x y => by
      have e : ∀ x0 : X, pair x0 y = Function.update (pair 0 y) false (ULift.up x0) := by
        intro x0; funext b; cases b <;> rfl
      rw [e (c • x), e x]
      exact (PiTensorProduct.tprod K).map_update_smul (pair 0 y) false c (ULift.up x))
    (fun x y y' => by
      have e : ∀ y0 : Y, pair x y0 = Function.update (pair x 0) true (ULift.up y0) := by
        intro y0; funext b; cases b <;> rfl
      rw [e (y + y'), e y, e y']
      exact (PiTensorProduct.tprod K).map_update_add (pair x 0) true (ULift.up y) (ULift.up y'))
    (fun c x y => by
      have e : ∀ y0 : Y, pair x y0 = Function.update (pair x 0) true (ULift.up y0) := by
        intro y0; funext b; cases b <;> rfl
      rw [e (c • y), e y]
      exact (PiTensorProduct.tprod K).map_update_smul (pair x 0) true c (ULift.up y))


def purePair : X →ₗ[K] Y →ₗ[K] Projective K X Y :=
  LinearMap.mk₂ K (fun x y => pure (K := K) x y)
    (fun x x' y => by change algebraicInclusion (algebraicPair (x + x') y) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)
    (fun c x y => by change algebraicInclusion (algebraicPair (c • x) y) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)
    (fun x y y' => by change algebraicInclusion (algebraicPair x (y + y')) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)
    (fun c x y => by change algebraicInclusion (algebraicPair x (c • y)) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)

lemma pure_eq (x : X) (y : Y) : pure (K := K) x y = purePair x y := rfl

lemma pure_norm (x : X) (y : Y) : ‖pure (K := K) x y‖ = ‖x‖ * ‖y‖ :=
  (projective_crossnorm_ball (K := K) (X := X) (Y := Y)).1 x y

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]

-- Functoriality of the completed projective product.
def mapBilinear (A : X →L[K] E) (B : Y →L[K] F) : Bilinear K X Y (Projective K E F) :=
  MultilinearMap.mkContinuous
    { toFun := fun m => pure (A (m false).down) (B (m true).down)
      map_update_add' := by
        intro _ m i p q
        cases i
        · simp only [Function.update_self, Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change pure (A (p.down + q.down)) (B (m true).down) = _
          simp only [map_add, pure_eq, LinearMap.add_apply]
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          change pure (A (m false).down) (B (p.down + q.down)) = _
          simp only [map_add, pure_eq, LinearMap.add_apply]
      map_update_smul' := by
        intro _ m i c p
        cases i
        · simp only [Function.update_self, Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change pure (A (c • p.down)) (B (m true).down) = _
          simp only [map_smul, pure_eq, LinearMap.smul_apply]
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          change pure (A (m false).down) (B (c • p.down)) = _
          simp only [map_smul, pure_eq, LinearMap.smul_apply] }
    (‖A‖ * ‖B‖) (by
      intro m
      change ‖pure (K := K) (A (m false).down) (B (m true).down)‖ ≤ ‖A‖ * ‖B‖ * ∏ i : Bool, ‖m i‖
      simp only [Fintype.prod_bool]
      change _ ≤ ‖A‖ * ‖B‖ * (‖(m true).down‖ * ‖(m false).down‖)
      rw [pure_norm]
      calc _ ≤ (‖A‖ * ‖(m false).down‖) * (‖B‖ * ‖(m true).down‖) :=
              mul_le_mul (A.le_opNorm _) (B.le_opNorm _) (norm_nonneg _) (by positivity)
        _ = _ := by ring)

def tensorMap (A : X →L[K] E) (B : Y →L[K] F) :
    Projective K X Y →L[K] Projective K E F := extendBilinear (mapBilinear A B)

lemma tensorMap_pure (A : X →L[K] E) (B : Y →L[K] F) (x : X) (y : Y) :
    tensorMap A B (pure x y) = pure (A x) (B y) := by
  exact (bilinear_extension (K := K) (X := X) (Y := Y) (Z := Projective K E F)).2.1 _ x y

lemma tensorMap_norm (A : X →L[K] E) (B : Y →L[K] F) : ‖tensorMap A B‖ ≤ ‖A‖ * ‖B‖ := by
  obtain ⟨I, hI, _⟩ := (bilinear_extension (K := K) (X := X) (Y := Y) (Z := Projective K E F)).1
  calc
    ‖tensorMap A B‖ = ‖mapBilinear A B‖ := by rw [tensorMap, ← hI, I.norm_map]
    _ ≤ ‖A‖ * ‖B‖ := MultilinearMap.mkContinuous_norm_le _ (by positivity) _

lemma tensorMap_contract (A : X →L[K] E) (B : Y →L[K] F) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (z : Projective K X Y) : ‖tensorMap A B z‖ ≤ ‖z‖ := by
  have hn : ‖tensorMap A B‖ ≤ 1 := (tensorMap_norm A B).trans (by
    calc _ ≤ 1 * 1 := mul_le_mul hA hB (norm_nonneg _) zero_le_one
         _ = 1 := one_mul _)
  exact ((tensorMap A B).le_opNorm z).trans (mul_le_of_le_one_left (norm_nonneg _) hn)

lemma ext_pure {L M : Projective K X Y →L[K] Projective K E F}
    (h : ∀ x y, L (pure x y) = M (pure x y)) : L = M := by
  have hres (x : X) (y : Y) : restrictBilinear M (pair x y) = M (pure x y) := rfl
  have hL := (bilinear_extension (K := K) (X := X) (Y := Y) (Z := Projective K E F)).2.2.1
    (restrictBilinear M) L (fun x y => (h x y).trans (hres x y).symm)
  have hM := (bilinear_extension (K := K) (X := X) (Y := Y) (Z := Projective K E F)).2.2.1
    (restrictBilinear M) M (fun x y => (hres x y).symm)
  exact hL.trans hM.symm

lemma complemented_norm (A : X →L[K] E) (B : Y →L[K] F)
    (i : E →L[K] X) (j : F →L[K] Y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hi : ‖i‖ ≤ 1) (hj : ‖j‖ ≤ 1)
    (hAi : ∀ x, A (i x) = x) (hBj : ∀ y, B (j y) = y)
    (z : Projective K E F) : ‖tensorMap i j z‖ = ‖z‖ := by
  have hcomp : (tensorMap A B).comp (tensorMap i j) = ContinuousLinearMap.id K _ := by
    apply ext_pure
    intro x y
    simp only [ContinuousLinearMap.comp_apply, tensorMap_pure, hAi, hBj, ContinuousLinearMap.id_apply]
  apply le_antisymm (tensorMap_contract i j hi hj z)
  have hz : tensorMap A B (tensorMap i j z) = z := DFunLike.congr_fun hcomp z
  calc ‖z‖ = ‖tensorMap A B (tensorMap i j z)‖ := congrArg norm hz.symm
       _ ≤ ‖tensorMap i j z‖ := tensorMap_contract A B hA hB _

lemma map_attains (A : X →L[K] E) (B : Y →L[K] F)
    (i : E →L[K] X) (j : F →L[K] Y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hi : ‖i‖ ≤ 1) (hj : ‖j‖ ≤ 1)
    (hAi : ∀ x, A (i x) = x) (hBj : ∀ y, B (j y) = y)
    (hin : ∀ x, ‖i x‖ = ‖x‖) (hjn : ∀ y, ‖j y‖ = ‖y‖)
    {z : Projective K E F} (hz : TensorAttains z) : TensorAttains (tensorMap i j z) := by
  obtain ⟨x, y, ⟨⟨C, hC⟩, hs, hsum⟩, hcost⟩ := hz
  refine ⟨fun n => i (x n), fun n => j (y n), ⟨⟨C, ?_⟩, ?_, ?_⟩, ?_⟩
  · simpa only [hin, hjn] using hC
  · simpa only [hin, hjn] using hs
  · simpa only [tensorMap_pure] using (tensorMap i j).hasSum hsum
  · simpa only [hin, hjn, complemented_norm A B i j hA hB hi hj hAi hBj] using hcost

lemma approx_sum (A : X →L[K] E) (B : Y →L[K] F)
    (i : E →L[K] X) (j : F →L[K] Y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hi : ‖i‖ ≤ 1) (hj : ‖j‖ ≤ 1)
    (hAi : ∀ x, A (i x) = x) (hBj : ∀ y, B (j y) = y)
    (hin : ∀ x, ‖i x‖ = ‖x‖) (hjn : ∀ y, ‖j y‖ = ‖y‖)
    (hd : TensorDense K E F) {n : ℕ} (x : Fin n → X) (y : Fin n → Y)
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η)
    (hx : ∀ k, ‖x k - i (A (x k))‖ ≤ 2 * δ * ‖x k‖)
    (hy : ∀ k, ‖y k - j (B (y k))‖ ≤ 2 * δ * ‖y k‖) :
    ∃ w : Projective K X Y, TensorAttains w ∧
      ‖(∑ k, pure (K := K) (x k) (y k)) - w‖ < 4 * δ * (∑ k, ‖x k‖ * ‖y k‖) + η := by
  let z : Projective K E F := ∑ k, pure (K := K) (A (x k)) (B (y k))
  obtain ⟨v, hdist, hv⟩ := (Metric.dense_iff.mp hd) z η hη
  refine ⟨tensorMap i j v, map_attains A B i j hA hB hi hj hAi hBj hin hjn hv, ?_⟩
  have hAx (k) : ‖i (A (x k))‖ ≤ ‖x k‖ := by
    rw [hin]; exact (A.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hA)
  have ht (k) : ‖pure (K := K) (x k) (y k) - pure (i (A (x k))) (j (B (y k)))‖ ≤
      4 * δ * (‖x k‖ * ‖y k‖) := by
    have he : pure (K := K) (x k) (y k) - pure (i (A (x k))) (j (B (y k))) =
        pure (x k - i (A (x k))) (y k) + pure (i (A (x k))) (y k - j (B (y k))) := by
      simp only [pure_eq, map_sub, LinearMap.sub_apply]; abel
    rw [he]
    calc _ ≤ ‖pure (K := K) (x k - i (A (x k))) (y k)‖ +
          ‖pure (K := K) (i (A (x k))) (y k - j (B (y k)))‖ := norm_add_le _ _
      _ ≤ (2 * δ * ‖x k‖) * ‖y k‖ + ‖x k‖ * (2 * δ * ‖y k‖) := by
        rw [pure_norm, pure_norm]
        gcongr
        · exact hx k
        · exact hAx k
        · exact hy k
      _ = _ := by ring
  have he : ‖(∑ k, pure (K := K) (x k) (y k)) - tensorMap i j z‖ ≤
      4 * δ * (∑ k, ‖x k‖ * ‖y k‖) := by
    simp only [z, map_sum, tensorMap_pure, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k, ‖pure (K := K) (x k) (y k) - pure (i (A (x k))) (j (B (y k)))‖ := norm_sum_le _ _
      _ ≤ ∑ k, 4 * δ * (‖x k‖ * ‖y k‖) := Finset.sum_le_sum fun k _ => ht k
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hvd : ‖tensorMap i j z - tensorMap i j v‖ < η := by
    rw [← map_sub]
    exact (tensorMap_contract i j hi hj _).trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hdist)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt (add_lt_add_of_le_of_lt he hvd)

-- Normalizing the finite test set turns MetricPi into strong approximation by a projection.
theorem projection_approx {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] (h : MetricPi K E) (t : Finset E)
    (δ : ℝ) (hδ : 0 < δ) : ∃ P : E →L[K] E, P.comp P = P ∧ ‖P‖ ≤ 1 ∧ FiniteDimensional K P.range ∧
      ∀ x ∈ t, ‖x - P x‖ ≤ 2 * δ * ‖x‖ := by
  classical
  let t' := (t.filter (· ≠ 0)).image (fun x => ((‖x‖ : K))⁻¹ • x)
  have hunit : ∀ x : E, x ≠ 0 → ‖((‖x‖ : K))⁻¹ • x‖ = 1 := by
    intro x hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hx0, inv_mul_cancel₀ hx0.ne']
  obtain ⟨P, h1, h2, h3, h4⟩ := h δ hδ t' (by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    exact hunit x' (Finset.mem_filter.1 hx').2)
  refine ⟨P, h1, h2, h3, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set u := ((‖x‖ : K))⁻¹ • x with hu
  have hut : u ∈ t' := Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hx, hx0⟩, rfl⟩
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := h4 u hut
  have hPy : P (P w) = P w := by
    have := congrArg (fun T : E →L[K] E => T w) h1
    simpa using this
  have hy' : ‖u - P w‖ < δ := hy
  have hb : ‖u - P u‖ ≤ 2 * δ := by
    have e : u - P u = (u - P w) - P (u - P w) := by rw [map_sub, hPy]; abel
    rw [e]
    calc ‖(u - P w) - P (u - P w)‖ ≤ ‖u - P w‖ + ‖P (u - P w)‖ := norm_sub_le _ _
      _ ≤ ‖u - P w‖ + ‖u - P w‖ := by
          gcongr
          exact (P.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) h2)
      _ ≤ 2 * δ := by linarith
  have hxu : x = ((‖x‖ : K)) • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hxp.ne'), one_smul]
  rw [hxu, map_smul, ← smul_sub, norm_smul, RCLike.norm_ofReal, abs_of_pos hxp]
  rw [← hxu]
  nlinarith

lemma range_norm_le (P : X →L[K] X) (hP : ‖P‖ ≤ 1) : ‖P.rangeRestrict‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound P.rangeRestrict zero_le_one
  intro x
  change ‖P x‖ ≤ 1 * ‖x‖
  exact (P.le_opNorm x).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg x))

lemma range_retract (P : X →L[K] X) (hP : P.comp P = P) (x : P.range) :
    P.rangeRestrict (P.range.subtypeL x) = x := by
  apply Subtype.ext
  obtain ⟨u, hu⟩ := x.property
  change P (x : X) = (x : X)
  rw [← hu]
  exact DFunLike.congr_fun hP u

lemma approx_algebraic (hX : MetricPi K X) (hY : MetricPi K Y ∨ UniformConvexSpace Y)
    (u : Algebraic K X Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : Projective K X Y, TensorAttains w ∧ ‖algebraicInclusion u - w‖ < ε := by
  classical
  obtain ⟨r, ⟨n, x, y, hu, hr⟩⟩ := ((projective_series (K := K) (X := X) (Y := Y)).2.1 u).1
  let M := ∑ k, ‖x k‖ * ‖y k‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let δ := ε / (16 * (M + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (16 * (M + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hlim : 4 * δ * M + ε / 2 < ε := by nlinarith [mul_nonneg hδ.le hM]
  obtain ⟨P, hP, hnP, hfP, haP⟩ := projection_approx (K := K) hX (Finset.univ.image x) δ hδ
  letI : FiniteDimensional K P.range := hfP
  have hx (k) : ‖x k - P.range.subtypeL (P.rangeRestrict (x k))‖ ≤ 2 * δ * ‖x k‖ :=
    haP _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have hsum : algebraicInclusion u = ∑ k, pure (K := K) (x k) (y k) := by
    rw [hu, map_sum]; rfl
  rcases hY with hY | hY
  · obtain ⟨Q, hQ, hnQ, hfQ, haQ⟩ := projection_approx (K := K) hY (Finset.univ.image y) δ hδ
    letI : FiniteDimensional K Q.range := hfQ
    have hy (k) : ‖y k - Q.range.subtypeL (Q.rangeRestrict (y k))‖ ≤ 2 * δ * ‖y k‖ :=
      haQ _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    have hd : TensorDense K P.range Q.range := by
      have heq : {z : Projective K P.range Q.range | TensorAttains z} = Set.univ := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact finite_dimensional_tensors z
      unfold TensorDense
      rw [heq]; exact dense_univ
    obtain ⟨w, hw, he⟩ := approx_sum P.rangeRestrict Q.rangeRestrict P.range.subtypeL Q.range.subtypeL
      (range_norm_le P hnP) (range_norm_le Q hnQ) (Submodule.norm_subtypeL_le _) (Submodule.norm_subtypeL_le _)
      (range_retract P hP) (range_retract Q hQ) (fun _ => rfl) (fun _ => rfl)
      hd x y δ (ε / 2) hδ (half_pos hε) hx hy
    refine ⟨w, hw, ?_⟩
    rw [hsum]; exact he.trans hlim
  · letI : UniformConvexSpace Y := hY
    have hd : TensorDense K P.range Y := finite_uniform_tensor_density
    have hnId : ‖ContinuousLinearMap.id K Y‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hy (k) : ‖y k - ContinuousLinearMap.id K Y (ContinuousLinearMap.id K Y (y k))‖ ≤
        2 * δ * ‖y k‖ := by simp only [ContinuousLinearMap.id_apply, sub_self, norm_zero]; positivity
    obtain ⟨w, hw, he⟩ := approx_sum P.rangeRestrict (ContinuousLinearMap.id K Y)
      P.range.subtypeL (ContinuousLinearMap.id K Y)
      (range_norm_le P hnP) hnId (Submodule.norm_subtypeL_le _) hnId
      (range_retract P hP) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hd x y δ (ε / 2) hδ (half_pos hε) hx hy
    refine ⟨w, hw, ?_⟩
    rw [hsum]; exact he.trans hlim

lemma density (hX : MetricPi K X) (hY : MetricPi K Y ∨ UniformConvexSpace Y) :
    TensorDense K X Y := by
  apply Metric.dense_iff.2
  intro z ε hε
  obtain ⟨u, hu⟩ := (projective_series (K := K) (X := X) (Y := Y)).2.2.2.1.exists_dist_lt z (half_pos hε)
  obtain ⟨w, hw, he⟩ := approx_algebraic hX hY u (ε / 2) (half_pos hε)
  refine ⟨w, ?_, hw⟩
  change dist w z < ε
  rw [dist_comm w z]
  calc
    dist z w ≤ dist z (algebraicInclusion u) + dist (algebraicInclusion u) w := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa only [dist_comm] using hu) (by simpa only [dist_eq_norm] using he)
    _ = ε := by ring

end X9Metric

variable {K : Type*} [RCLike K]
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

theorem solution (hX : MetricPi K X) :
    (MetricPi K Y → TensorDense K X Y) ∧
    (UniformConvexSpace Y → TensorDense K X Y) := by
  exact ⟨fun hY => X9Metric.density hX (Or.inl hY), fun hY => X9Metric.density hX (Or.inr hY)⟩
