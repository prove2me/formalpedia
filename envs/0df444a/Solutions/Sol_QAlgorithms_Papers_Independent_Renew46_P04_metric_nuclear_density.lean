-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.metric_nuclear_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:00:18.049243+00:00
-- url     : https://prove2.me/submissions/2d73b37c-b28e-4d8d-9698-656e54db2c62

import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_projective_series
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_projective_crossnorm_ball
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_extension
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_metric_tensor_density
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

namespace X9MetricNuclear
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

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

lemma ext_pure_general {L M : Projective K X Y →L[K] Z}
    (h : ∀ x y, L (pure x y) = M (pure x y)) : L = M := by
  have hL := (bilinear_extension (K := K) (X := X) (Y := Y) (Z := Z)).2.2.1
    (restrictBilinear M) L (fun x y => h x y)
  have hM := (bilinear_extension (K := K) (X := X) (Y := Y) (Z := Z)).2.2.1
    (restrictBilinear M) M (fun _ _ => rfl)
  exact hL.trans hM.symm

def ofCurried (A : X →L[K] Y →L[K] Z) : Bilinear K X Y Z :=
  MultilinearMap.mkContinuous
    { toFun := fun m => A (m false).down (m true).down
      map_update_add' := by
        intro _ m i p q
        cases i
        · simp only [Function.update_self, Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change A (p.down + q.down) (m true).down = _
          simp only [map_add, ContinuousLinearMap.add_apply]
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          change A (m false).down (p.down + q.down) = _
          exact map_add _ _ _
      map_update_smul' := by
        intro _ m i c p
        cases i
        · simp only [Function.update_self, Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change A (c • p.down) (m true).down = _
          simp only [map_smul, ContinuousLinearMap.smul_apply]
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          change A (m false).down (c • p.down) = _
          exact map_smul _ _ _ }
    ‖A‖ (by
      intro m
      change ‖A (m false).down (m true).down‖ ≤ ‖A‖ * ∏ i : Bool, ‖m i‖
      simp only [Fintype.prod_bool]
      change _ ≤ ‖A‖ * (‖(m true).down‖ * ‖(m false).down‖)
      calc _ ≤ ‖A (m false).down‖ * ‖(m true).down‖ := (A _).le_opNorm _
        _ ≤ (‖A‖ * ‖(m false).down‖) * ‖(m true).down‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ = _ := by ring)

def leftSlice (f : X →L[K] K) : Projective K X Y →L[K] Y :=
  extendBilinear (ofCurried (f.smulRight (ContinuousLinearMap.id K Y)))

def rightSlice (g : Y →L[K] K) : Projective K X Y →L[K] X :=
  extendBilinear (ofCurried (g.smulRight (ContinuousLinearMap.id K X)).flip)

lemma leftSlice_pure (f : X →L[K] K) (x : X) (y : Y) :
    leftSlice f (pure x y) = f x • y := by
  exact (bilinear_extension (K := K) (X := X) (Y := Y) (Z := Y)).2.1 _ x y

lemma rightSlice_pure (g : Y →L[K] K) (x : X) (y : Y) :
    rightSlice g (pure x y) = g y • x := by
  exact (bilinear_extension (K := K) (X := X) (Y := Y) (Z := X)).2.1 _ x y

lemma realization_pure (f : X →L[K] K) (y : Y) :
    projectiveRealization (K := K) (X := X) (Y := Y) (pure f y) = f.smulRight y :=
  (bilinear_extension (K := K) (X := X →L[K] K) (Y := Y) (Z := X →L[K] Y)).2.1 _ f y

-- A tensor in the realization kernel has all of its scalar slices equal to zero.
lemma rightSlice_kernel (z : Projective K (X →L[K] K) Y)
    (hz : projectiveRealization z = 0) (g : Y →L[K] K) : rightSlice g z = 0 := by
  ext x
  have he : (ContinuousLinearMap.apply K K x).comp (rightSlice g) =
      g.comp ((ContinuousLinearMap.apply K Y x).comp (projectiveRealization (K := K))) := by
    apply ext_pure_general
    intro f y
    simp only [ContinuousLinearMap.comp_apply, rightSlice_pure, realization_pure,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul]
    exact mul_comm _ _
  have hx := DFunLike.congr_fun he z
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    hz, ContinuousLinearMap.zero_apply, map_zero] using hx

lemma leftSlice_kernel (z : Projective K (X →L[K] K) Y)
    (hz : projectiveRealization z = 0) (f : (X →L[K] K) →L[K] K) : leftSlice f z = 0 := by
  apply NormedSpace.eq_zero_of_forall_dual_eq_zero K
  intro g
  have he : g.comp (leftSlice f) = f.comp (rightSlice g) := by
    apply ext_pure_general
    intro a y
    simp only [ContinuousLinearMap.comp_apply, leftSlice_pure, rightSlice_pure,
      map_smul, smul_eq_mul]
    exact mul_comm _ _
  have hez := DFunLike.congr_fun he z
  simpa only [ContinuousLinearMap.comp_apply, rightSlice_kernel z hz g, map_zero] using hez

def pureRight (x : X) : Y →L[K] Projective K X Y :=
  (purePair x).mkContinuous ‖x‖ (fun y => (pure_norm x y).le)

lemma pureRight_apply (x : X) (y : Y) : pureRight x y = pure (K := K) x y := rfl

lemma finite_rank_kernel (P : (X →L[K] K) →L[K] (X →L[K] K))
    [FiniteDimensional K P.range] (z : Projective K (X →L[K] K) Y)
    (hz : projectiveRealization z = 0) :
    tensorMap P (ContinuousLinearMap.id K Y) z = 0 := by
  classical
  let b := Module.finBasis K P.range
  let c (i : Fin (Module.finrank K P.range)) : (X →L[K] K) →L[K] K :=
    (b.coord i).toContinuousLinearMap.comp P.rangeRestrict
  have he : tensorMap P (ContinuousLinearMap.id K Y) =
      ∑ i, (pureRight (b i : X →L[K] K)).comp (leftSlice (c i)) := by
    apply ext_pure_general
    intro f y
    simp only [tensorMap_pure, ContinuousLinearMap.id_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, leftSlice_pure, pureRight_apply]
    have hb : ∑ i, c i f • (b i : X →L[K] K) = P f := by
      have hb' := congrArg (fun a : P.range => (a : X →L[K] K)) (b.sum_repr (P.rangeRestrict f))
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hb'
      convert hb' using 1 <;> rfl
    rw [← hb]
    simp only [pure_eq, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [he, ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [ContinuousLinearMap.comp_apply, leftSlice_kernel z hz, map_zero]

lemma tensor_projection_approx (hX : MetricPi K X) (z : Projective K X Y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : X →L[K] X, ‖P‖ ≤ 1 ∧ FiniteDimensional K P.range ∧
      ‖z - tensorMap P (ContinuousLinearMap.id K Y) z‖ < ε := by
  classical
  obtain ⟨u, hu⟩ := (projective_series (K := K) (X := X) (Y := Y)).2.2.2.1.exists_dist_lt z
    (by positivity : 0 < ε / 4)
  have huz : ‖z - algebraicInclusion u‖ < ε / 4 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hu
  obtain ⟨r, ⟨n, x, y, heq, hr⟩⟩ := ((projective_series (K := K) (X := X) (Y := Y)).2.1 u).1
  let M := ∑ k, ‖x k‖ * ‖y k‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let δ := ε / (8 * (M + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (8 * (M + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  obtain ⟨P, _, hnP, hfP, haP⟩ := projection_approx (K := K) hX (Finset.univ.image x) δ hδ
  refine ⟨P, hnP, hfP, ?_⟩
  let L := tensorMap P (ContinuousLinearMap.id K Y)
  have hcontract (a : Projective K X Y) : ‖L a‖ ≤ ‖a‖ :=
    tensorMap_contract P _ hnP ContinuousLinearMap.norm_id_le a
  have hsum : algebraicInclusion u = ∑ k, pure (K := K) (x k) (y k) := by
    rw [heq, map_sum]; rfl
  have huf : ‖algebraicInclusion u - L (algebraicInclusion u)‖ ≤ 2 * δ * M := by
    rw [hsum]
    simp only [L, map_sum, tensorMap_pure, ContinuousLinearMap.id_apply, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ k, ‖pure (K := K) (x k) (y k) - pure (P (x k)) (y k)‖ := norm_sum_le _ _
      _ = ∑ k, ‖x k - P (x k)‖ * ‖y k‖ := by
        congr 1; ext k
        rw [← pure_norm (K := K) (x k - P (x k)) (y k)]
        congr 1
        simp only [pure_eq, map_sub, LinearMap.sub_apply]
      _ ≤ ∑ k, 2 * δ * ‖x k‖ * ‖y k‖ := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right
          (haP _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)) (norm_nonneg _)
      _ = 2 * δ * M := by dsimp [M]; rw [Finset.mul_sum]; congr 1; ext k; ring
  have hdiff : ‖L (algebraicInclusion u) - L z‖ < ε / 4 := by
    rw [← map_sub]
    exact (hcontract _).trans_lt (by simpa only [norm_sub_rev] using huz)
  calc
    ‖z - L z‖ ≤ ‖z - algebraicInclusion u‖ +
      (‖algebraicInclusion u - L (algebraicInclusion u)‖ + ‖L (algebraicInclusion u) - L z‖) :=
        (norm_sub_le_norm_sub_add_norm_sub z (algebraicInclusion u) (L z)).trans
          (add_le_add le_rfl
            (norm_sub_le_norm_sub_add_norm_sub (algebraicInclusion u) (L (algebraicInclusion u)) (L z)))
    _ < ε / 4 + (2 * δ * M + ε / 4) := add_lt_add huz (add_lt_add_of_le_of_lt huf hdiff)
    _ < ε := by nlinarith

lemma realization_kernel_zero (hX : MetricPi K (X →L[K] K))
    (z : Projective K (X →L[K] K) Y) (hz : projectiveRealization z = 0) : z = 0 := by
  by_contra hnz
  obtain ⟨P, _, hfP, he⟩ := tensor_projection_approx hX z ‖z‖ (norm_pos_iff.mpr hnz)
  letI : FiniteDimensional K P.range := hfP
  rw [finite_rank_kernel P z hz, sub_zero] at he
  exact (lt_irrefl _ he)

lemma quotient_norm_le (z : Projective K (X →L[K] K) Y) :
    ‖nuclearQuotient (K := K) (X := X) (Y := Y) z‖ ≤ ‖z‖ :=
  Submodule.Quotient.norm_mk_le _ z

lemma quotient_norm (hX : MetricPi K (X →L[K] K)) (z : Projective K (X →L[K] K) Y) :
    ‖nuclearQuotient (K := K) (X := X) (Y := Y) z‖ = ‖z‖ := by
  apply le_antisymm (quotient_norm_le z)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, ha, han⟩ := Submodule.Quotient.norm_mk_lt (nuclearQuotient (K := K) (X := X) (Y := Y) z) hε
  have hqa : nuclearQuotient (K := K) (X := X) (Y := Y) a = nuclearQuotient z := ha
  have hJa : projectiveRealization (K := K) (X := X) (Y := Y) a = projectiveRealization z :=
    congrArg nuclearOperator hqa
  have haz : a = z := sub_eq_zero.mp (realization_kernel_zero hX (a - z) (by rw [map_sub, hJa, sub_self]))
  simpa only [haz] using han.le

lemma map_attains (hX : MetricPi K (X →L[K] K)) {z : Projective K (X →L[K] K) Y}
    (hz : TensorAttains z) : NuclearAttains (nuclearQuotient (X := X) z) := by
  obtain ⟨f, y, hrep, hcost⟩ := hz
  refine ⟨f, y, ⟨hrep.1, hrep.2.1, fun x => ?_⟩, ?_⟩
  · have hs := (hrep.2.2.map (projectiveRealization (K := K) (X := X) (Y := Y))
      (projectiveRealization (K := K) (X := X) (Y := Y)).continuous).map
      (ContinuousLinearMap.apply K Y x) (ContinuousLinearMap.apply K Y x).continuous
    convert hs using 1
    · funext n
      simp [realization_pure]
    · rfl
  · rw [quotient_norm hX]
    exact hcost

lemma density (hX : MetricPi K (X →L[K] K)) (hd : TensorDense K (X →L[K] K) Y) :
    NuclearDense K X Y := by
  apply Metric.dense_iff.2
  intro T ε hε
  obtain ⟨z, rfl⟩ := (projectiveRealization (K := K) (X := X) (Y := Y)).ker.mkQ_surjective T
  obtain ⟨w, hw, ha⟩ := Metric.dense_iff.mp hd z ε hε
  refine ⟨nuclearQuotient w, ?_, map_attains hX ha⟩
  simp only [Metric.mem_ball, dist_eq_norm]
  change ‖nuclearQuotient (K := K) (X := X) (Y := Y) w - nuclearQuotient z‖ < ε
  rw [← map_sub]
  exact (quotient_norm_le _).trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hw)

end X9MetricNuclear

variable {K : Type*} [RCLike K]
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

theorem solution (hX : MetricPi K (X →L[K] K)) :
    (MetricPi K Y → NuclearDense K X Y) ∧
    (UniformConvexSpace Y → NuclearDense K X Y) := by
  obtain ⟨ha, hb⟩ := metric_tensor_density hX (Y := Y)
  exact ⟨fun hY => X9MetricNuclear.density hX (ha hY), fun hY => X9MetricNuclear.density hX (hb hY)⟩

