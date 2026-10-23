-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.attaining_operators_norming
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:50:47.341205+00:00
-- url     : https://prove2.me/submissions/765e3494-c8f6-4197-ad65-6d86e1cfe0fe

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

set_option synthInstance.maxSize 8192

namespace QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set

open scoped Topology TensorProduct ENNReal

variable {K : Type*} [RCLike K]

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

section X7NormingSec

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace K X]
variable [NormedAddCommGroup Y] [NormedSpace K Y]

theorem X7N_dense : DenseRange (algebraicInclusion (K := K) (X := X) (Y := Y)) := by
  have h1 : DenseRange (fun a : NormedAlgebraic K X Y =>
      (a : UniformSpace.Completion (NormedAlgebraic K X Y))) :=
    UniformSpace.Completion.denseRange_coe
  have h2 : DenseRange (SeparationQuotient.mk : Algebraic K X Y → NormedAlgebraic K X Y) :=
    SeparationQuotient.surjective_mk.denseRange
  exact h1.comp h2 (UniformSpace.Completion.continuous_coe _)

theorem X7N_unif : IsUniformInducing (algebraicInclusion (K := K) (X := X) (Y := Y)) :=
  (UniformSpace.Completion.isUniformInducing_coe _).comp SeparationQuotient.isUniformInducing_mk

theorem X7N_norm_pure (x : X) (y : Y) : ‖pure (K := K) x y‖ ≤ ‖x‖ * ‖y‖ := by
  unfold pure algebraicInclusion
  change ‖((SeparationQuotient.mk (PiTensorProduct.tprod K (pair x y)) :
      NormedAlgebraic K X Y) : UniformSpace.Completion (NormedAlgebraic K X Y))‖ ≤ _
  rw [UniformSpace.Completion.norm_coe, SeparationQuotient.norm_mk]
  refine (PiTensorProduct.projectiveSeminorm_tprod_le (pair x y)).trans (le_of_eq ?_)
  rw [Fintype.prod_bool, mul_comm]
  rfl

def X7N_fx (x : X) : Factors X Y false := ULift.up x

def X7N_fy (y : Y) : Factors X Y true := ULift.up y

theorem X7N_updF (x x' : X) (y : Y) :
    Function.update (pair x y) false (X7N_fx (Y := Y) x') = pair x' y := by
  funext b; cases b <;> rfl

theorem X7N_updT (x : X) (y y' : Y) :
    Function.update (pair x y) true (X7N_fy (X := X) y') = pair x y' := by
  funext b; cases b <;> rfl

theorem X7N_pair_eta (m : (b : Bool) → Factors X Y b) :
    pair (m false).down (m true).down = m := by
  funext b; cases b <;> rfl

/-- `B (pure x y)` as a bounded bilinear map. -/
def X7N_op (B : Projective K X Y →L[K] K) : X →L[K] (Y →L[K] K) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ K (fun x y => restrictBilinear B (pair x y))
      (fun x x' y => by
        have h := (restrictBilinear B).map_update_add (pair x y) false
          (X7N_fx (Y := Y) x) (X7N_fx x')
        have e : X7N_fx (Y := Y) x + X7N_fx x' = X7N_fx (x + x') := rfl
        rw [e, X7N_updF, X7N_updF, X7N_updF] at h
        exact h)
      (fun c x y => by
        have h := (restrictBilinear B).map_update_smul (pair x y) false c
          (X7N_fx (Y := Y) x)
        have e : c • X7N_fx (Y := Y) x = X7N_fx (c • x) := rfl
        rw [e, X7N_updF, X7N_updF] at h
        exact h)
      (fun x y y' => by
        have h := (restrictBilinear B).map_update_add (pair x y) true
          (X7N_fy (X := X) y) (X7N_fy y')
        have e : X7N_fy (X := X) y + X7N_fy y' = X7N_fy (y + y') := rfl
        rw [e, X7N_updT, X7N_updT, X7N_updT] at h
        exact h)
      (fun c x y => by
        have h := (restrictBilinear B).map_update_smul (pair x y) true c
          (X7N_fy (X := X) y)
        have e : c • X7N_fy (X := X) y = X7N_fy (c • y) := rfl
        rw [e, X7N_updT, X7N_updT] at h
        exact h))
    ‖B‖ (fun x y => by
      change ‖B (pure x y)‖ ≤ ‖B‖ * ‖x‖ * ‖y‖
      calc ‖B (pure x y)‖ ≤ ‖B‖ * ‖pure (K := K) x y‖ := B.le_opNorm _
        _ ≤ ‖B‖ * (‖x‖ * ‖y‖) := by gcongr; exact X7N_norm_pure x y
        _ = ‖B‖ * ‖x‖ * ‖y‖ := by ring)

theorem X7N_op_apply (B : Projective K X Y →L[K] K) (x : X) (y : Y) :
    X7N_op B x y = B (pure x y) := rfl

theorem X7N_op_norm (B : Projective K X Y →L[K] K) : ‖X7N_op B‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

theorem X7N_tensorFunctional (B : Projective K X Y →L[K] K) :
    tensorFunctional (X7N_op B) = B := by
  unfold tensorFunctional extendBilinear
  apply ContinuousLinearMap.extend_unique
    (PiTensorProduct.liftIsometry K (Factors X Y) K (dualBilinear (X7N_op B)))
    (X7N_dense (K := K) (X := X) (Y := Y)) (X7N_unif (K := K) (X := X) (Y := Y))
  apply ContinuousLinearMap.coe_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro m
  simp only [LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, PiTensorProduct.liftIsometry_apply_apply,
    PiTensorProduct.lift.tprod]
  change B (algebraicInclusion (PiTensorProduct.tprod K m)) =
    B (algebraicInclusion (PiTensorProduct.tprod K (pair (m false).down (m true).down)))
  rw [X7N_pair_eta]

end X7NormingSec

section X7NormingMain

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

theorem X7N_main (h : TensorDense K X Y) :
    TensorNorming {T : X →L[K] (Y →L[K] K) | OperatorAttains T ∧ ‖T‖ ≤ 1} := by
  intro z hz eps heps
  set δ := min (eps / 2) (1 / 2) with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ eps / 2 := min_le_left _ _
  have hδ2 : δ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨w, hw, hzw⟩ := h.exists_dist_lt z hδ
  rw [dist_eq_norm] at hzw
  have hwn : 1 - δ < ‖w‖ := by
    have := norm_sub_norm_le z w
    linarith
  have hw0 : ‖w‖ ≠ 0 := by linarith
  obtain ⟨x, y, ⟨-, hs, hsum⟩, hnorm⟩ := hw
  obtain ⟨B, hB1, hBw⟩ := exists_dual_vector K w hw0
  set T := X7N_op B with hTdef
  have hT1 : ‖T‖ ≤ 1 := hB1 ▸ X7N_op_norm B
  -- real parts along the representation
  have hre : HasSum (fun n => RCLike.re (B (pure (x n) (y n)))) ‖w‖ := by
    have h1 := (hsum.map B B.continuous).map (RCLike.reCLM : K →L[ℝ] ℝ) RCLike.reCLM.continuous
    rw [hBw] at h1
    simp only [RCLike.reCLM_apply, RCLike.ofReal_re] at h1
    exact h1
  have hprod : HasSum (fun n => ‖x n‖ * ‖y n‖) ‖w‖ := by
    rw [hnorm]; exact hs.hasSum
  have hle : ∀ n, RCLike.re (B (pure (x n) (y n))) ≤ ‖x n‖ * ‖y n‖ := by
    intro n
    calc RCLike.re (B (pure (x n) (y n))) ≤ ‖B (pure (x n) (y n))‖ := RCLike.re_le_norm _
      _ ≤ ‖B‖ * ‖pure (K := K) (x n) (y n)‖ := B.le_opNorm _
      _ ≤ 1 * (‖x n‖ * ‖y n‖) := by rw [hB1]; gcongr; exact X7N_norm_pure _ _
      _ = ‖x n‖ * ‖y n‖ := one_mul _
  -- some term is nonzero
  obtain ⟨n0, hn0⟩ : ∃ n, 0 < ‖x n‖ * ‖y n‖ := by
    by_contra hc
    push_neg at hc
    have : ∀ n, ‖x n‖ * ‖y n‖ = 0 := fun n =>
      le_antisymm (hc n) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have h0 : HasSum (fun n => ‖x n‖ * ‖y n‖) 0 := by
      simp only [this]; exact hasSum_zero
    have := h0.unique hprod
    exact hw0 this.symm
  have heq : RCLike.re (B (pure (x n0) (y n0))) = ‖x n0‖ * ‖y n0‖ := by
    by_contra hne
    have hlt : RCLike.re (B (pure (x n0) (y n0))) < ‖x n0‖ * ‖y n0‖ :=
      lt_of_le_of_ne (hle n0) hne
    have := hasSum_lt (f := fun n => RCLike.re (B (pure (x n) (y n))))
      (g := fun n => ‖x n‖ * ‖y n‖) hle hlt hre hprod
    exact lt_irrefl _ this
  have hx0 : 0 < ‖x n0‖ := by
    rcases (norm_nonneg (x n0)).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul] at hn0; exact absurd hn0 (lt_irrefl _)
  have hy0 : 0 < ‖y n0‖ := by
    rcases (norm_nonneg (y n0)).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', mul_zero] at hn0; exact absurd hn0 (lt_irrefl _)
  set xh : X := ((‖x n0‖⁻¹ : ℝ) : K) • x n0
  set yh : Y := ((‖y n0‖⁻¹ : ℝ) : K) • y n0
  have hxh : ‖xh‖ = 1 := by
    simp only [xh, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
    field_simp
  have hyh : ‖yh‖ = 1 := by
    simp only [yh, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
    field_simp
  have hval : T xh yh = ((‖x n0‖⁻¹ * ‖y n0‖⁻¹ : ℝ) : K) * B (pure (x n0) (y n0)) := by
    simp only [xh, yh, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hTdef,
      X7N_op_apply]
    push_cast; ring
  have hge : 1 ≤ ‖T xh‖ := by
    calc (1 : ℝ) = (‖x n0‖⁻¹ * ‖y n0‖⁻¹) * RCLike.re (B (pure (x n0) (y n0))) := by
          rw [heq]; field_simp
      _ = RCLike.re (T xh yh) := by
          rw [hval, RCLike.re_ofReal_mul]
      _ ≤ ‖T xh yh‖ := RCLike.re_le_norm _
      _ ≤ ‖T xh‖ * ‖yh‖ := (T xh).le_opNorm _
      _ = ‖T xh‖ := by rw [hyh, mul_one]
  have hTx : ‖T xh‖ ≤ ‖T‖ := by
    have := T.le_opNorm xh
    rwa [hxh, mul_one] at this
  refine ⟨T, ⟨⟨xh, hxh, ?_⟩, hT1⟩, ?_⟩
  · linarith
  · rw [X7N_tensorFunctional]
    have h1 : ‖B w‖ = ‖w‖ := by rw [hBw]; simp
    have h2 : ‖B (z - w)‖ ≤ ‖z - w‖ := by
      have := B.le_opNorm (z - w); rw [hB1, one_mul] at this; exact this
    have h3 : ‖B w‖ - ‖B (z - w)‖ ≤ ‖B z‖ := by
      have e : B w = B z - B (z - w) := by rw [map_sub]; abel
      have := norm_sub_le (B z) (B (z - w))
      rw [← e] at this
      linarith
    linarith

end X7NormingMain

end QAlgorithms.Papers.Independent.Renew46.P04

noncomputable section

set_option synthInstance.maxSize 8192

open Filter Set

open scoped Topology TensorProduct ENNReal

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

open QAlgorithms.Papers.Independent.Renew46.P04 in
theorem solution {K : Type*} [RCLike K] {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y] (h : TensorDense K X Y) :
    TensorNorming {T : X →L[K] (Y →L[K] K) | OperatorAttains T ∧ ‖T‖ ≤ 1} :=
  X7N_main h

end
