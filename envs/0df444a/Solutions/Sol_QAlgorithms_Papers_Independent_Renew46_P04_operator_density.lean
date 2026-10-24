-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.operator_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T04:06:18.489595+00:00
-- url     : https://prove2.me/submissions/e8ffa86e-dc9d-434d-b8c3-26b83e6be157

import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_density

noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000

open QAlgorithms.Papers.Independent.Renew46.P04
attribute [local instance] linearOperatorNorm linearOperatorSeminormedGroup
attribute [local instance] linearOperatorNormedGroup linearOperatorNormedSpace
attribute [local instance] dualNormedGroup dualNormedSpace

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

theorem operatorAttains_of_bilinearAttains (B : Bilinear K X Y K)
    (hB : BilinearAttains B) : OperatorAttains (formOperator B) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hB
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · simpa [hx] using (formOperator B).le_opNorm x
  · rw [norm_formOperator, ← hxy, ← formOperator_apply]
    simpa [hy] using (formOperator B x).le_opNorm y

end X9
noncomputable section

set_option synthInstance.maxSize 8192

open QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

section Banach

variable {X Y Z : Type*}

variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

variable [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

theorem solution [CompleteSpace X] [CompleteSpace Y] [Nontrivial X]
    (h : ∀ z : Projective K X Y, TensorAttains z) :
    Dense {T : X →L[K] (Y →L[K] K) | OperatorAttains T} := by
  classical
  cases subsingleton_or_nontrivial Y with
  | inl hY =>
    apply Metric.dense_iff.2
    intro T eps heps
    refine ⟨T, by simpa using heps, ?_⟩
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have hT : T = 0 := by
      ext x y
      rw [Subsingleton.elim y 0, map_zero]
      rfl
    rw [hT]
    exact ⟨(‖x‖⁻¹ : K) • x, norm_smul_inv_norm hx, by simp⟩
  | inr hY =>
    apply Metric.dense_iff.2
    intro T eps heps
    obtain ⟨B, hBdist, hBatt⟩ := Metric.dense_iff.mp (bilinear_density h)
      (dualBilinear T) eps heps
    refine ⟨X9.formOperator B, ?_, X9.operatorAttains_of_bilinearAttains B hBatt⟩
    change dist (X9.formOperator B) T < eps
    rw [dist_eq_norm, ← X9.formOperator_dualBilinear T,
      ← X9.formOperator_sub, X9.norm_formOperator]
    simpa only [Metric.mem_ball, dist_eq_norm] using hBdist

end Banach
end
