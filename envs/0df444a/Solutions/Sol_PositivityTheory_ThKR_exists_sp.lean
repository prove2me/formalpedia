-- Prove2me | solution 1 for PositivityTheory.ThKR.exists_sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:06.080225+00:00
-- url     : https://prove2.me/submissions/f78b766f-cfeb-46ae-958c-c5e78e0e103a

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_ExistsSmoothFun
import Theorems.Thm_GlobalTheory_WeilM_IsTilde_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR
theorem _root_.solution (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') :
    ∃ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ (t : ℝ) w, s t w = NormedSpace.exp (t • X) *ᵥ w := by
  have hsJ : ∀ w w' : l ⊕ l → ℝ, GlobalTheory.RealWeil.sympl w w' = -(w ⬝ᵥ (Matrix.J l ℝ *ᵥ w')) := by
    intro w w'
    simp [GlobalTheory.RealWeil.sympl, GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart, Matrix.J, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks, PiLp.inner_apply, Matrix.one_apply]
    simp only [mul_comm]
    ring
  have hent : ∀ (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) i j, N i j = Pi.single i 1 ⬝ᵥ (N *ᵥ Pi.single j 1) := by
    intro N i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hinv : ∀ t, (LinearMap.toMatrix' (s t))ᵀ * Matrix.J l ℝ * LinearMap.toMatrix' (s t) = Matrix.J l ℝ := by
    intro t
    ext i j
    have h := ss t (Pi.single i 1) (Pi.single j 1)
    rw [hsJ, hsJ, neg_inj, ← LinearMap.toMatrix'_mulVec (s t), ← LinearMap.toMatrix'_mulVec (s t)] at h
    rw [hent ((LinearMap.toMatrix' (s t))ᵀ * Matrix.J l ℝ * LinearMap.toMatrix' (s t)) i j, hent (Matrix.J l ℝ) i j, ← h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  letI : NormedAddCommGroup (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  let Φ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => LinearMap.toMatrix' (s t)
  have hΦw : ∀ t w, s t w = Φ t *ᵥ w := fun t w => (LinearMap.toMatrix'_mulVec (s t) w).symm
  have hΦc : Continuous Φ := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [Φ, LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp (sc _)
  have hΦ0 : Φ 0 = 1 := by
    have : s 0 = LinearMap.id := LinearMap.ext s0
    simp only [Φ, this, LinearMap.toMatrix'_id]
  have hΦm : ∀ t u, Φ (t + u) = Φ t * Φ u := by
    intro t u
    have : s (t + u) = (s t).comp (s u) := LinearMap.ext fun w => sm t u w
    simp only [Φ, this, LinearMap.toMatrix'_comp]
  haveI : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _
  let G : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun x => ∫ u in (0 : ℝ)..x, Φ u
  have hG : ∀ x, HasDerivAt G (Φ x) x := fun x => (hΦc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hslope : Filter.Tendsto (fun h : ℝ => h⁻¹ • G h) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have h1 := (hasDerivAt_iff_tendsto_slope.1 (hG 0))
    have hG0 : G 0 = 0 := intervalIntegral.integral_same
    rw [hΦ0] at h1
    refine h1.congr fun h => ?_
    rw [slope_def_module, hG0, sub_zero, sub_zero]
  obtain ⟨h0, hh0, hsmall⟩ : ∃ h0 : ℝ, h0 ≠ 0 ∧ ‖1 - h0⁻¹ • G h0‖ < 1 := by
    have hev : ∀ᶠ h in nhdsWithin (0 : ℝ) {0}ᶜ, ‖1 - h⁻¹ • G h‖ < 1 := by
      have := (hslope.const_sub (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ)).norm
      simp only [sub_self, norm_zero] at this
      exact this.eventually (gt_mem_nhds one_pos)
    obtain ⟨h, hh, hm⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨h, hm, hh⟩
  let u : Matrix (l ⊕ l) (l ⊕ l) ℝ := h0⁻¹ • G h0
  let U : (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ := Units.oneSub (1 - u) hsmall
  have hU : (U : Matrix (l ⊕ l) (l ⊕ l) ℝ) = u := by simp [U, Units.val_oneSub]
  let Binv : Matrix (l ⊕ l) (l ⊕ l) ℝ := h0⁻¹ • ((U⁻¹ : (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ) : Matrix (l ⊕ l) (l ⊕ l) ℝ)
  have hGB : G h0 * Binv = 1 := by
    have e : G h0 = h0 • (U : Matrix (l ⊕ l) (l ⊕ l) ℝ) := by rw [hU]; simp only [u]; rw [smul_inv_smul₀ hh0]
    rw [e, smul_mul_smul_comm, mul_inv_cancel₀ hh0, Units.mul_inv, one_smul]
  have hshift : ∀ t, Φ t * G h0 = G (t + h0) - G t := by
    intro t
    have e1 : Φ t * G h0 = ∫ x in (0 : ℝ)..h0, Φ t * Φ x := by
      simpa using ((ContinuousLinearMap.mul ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) (Φ t)).intervalIntegral_comp_comm
        (hΦc.intervalIntegrable 0 h0)).symm
    rw [e1]
    simp_rw [← hΦm]
    rw [intervalIntegral.integral_comp_add_left (fun x => Φ x) t, add_zero]
    exact (intervalIntegral.integral_interval_sub_left (hΦc.intervalIntegrable 0 (t + h0))
      (hΦc.intervalIntegrable 0 t)).symm
  let A : Matrix (l ⊕ l) (l ⊕ l) ℝ := (Φ h0 - 1) * Binv
  have hΦd : ∀ t, HasDerivAt Φ (Φ t * A) t := by
    intro t
    have hrep : Φ = fun x => (G (x + h0) - G x) * Binv := by
      funext x
      rw [← hshift x, mul_assoc, hGB, mul_one]
    have hd := (((hG (t + h0)).comp_add_const t h0).sub (hG t)).mul_const Binv
    have hval : (Φ (t + h0) - Φ t) * Binv = Φ t * A := by
      rw [hΦm, ← mul_sub_one, mul_assoc]
    rw [hval] at hd
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => congrFun hrep x)
  have hE : ∀ t : ℝ, HasDerivAt (fun x : ℝ => NormedSpace.exp ((-x) • A)) (-(A * NormedSpace.exp ((-t) • A))) t := by
    intro t
    have h1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A (-t)).scomp t (hasDerivAt_neg t)
    exact h1.congr_deriv (by simp <;> rfl)
  have hP : ∀ t, Φ t * NormedSpace.exp ((-t) • A) = 1 := by
    intro t
    have hd : ∀ x, HasDerivAt (fun x => Φ x * NormedSpace.exp ((-x) • A)) 0 x := by
      intro x
      have h1 := (hΦd x).mul (hE x)
      exact h1.congr_deriv (by rw [mul_neg, mul_assoc, add_neg_cancel])
    have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
    rw [hc, hΦ0, neg_zero, zero_smul, NormedSpace.exp_zero, one_mul]
  letI : NormedAlgebra ℚ (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
    { (inferInstance : Algebra ℚ (Matrix (l ⊕ l) (l ⊕ l) ℝ)) with
      norm_smul_le := fun q M => by
        rw [← Rat.cast_smul_eq_qsmul ℝ q M, norm_smul, Rat.norm_cast_real] }
  have hΦe : ∀ t, Φ t = NormedSpace.exp (t • A) := by
    intro t
    have hcomm : Commute ((-t) • A) (t • A) := ((Commute.refl A).smul_left _).smul_right _
    have h1 : NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A) = 1 := by
      have h2 := (NormedSpace.exp_add_of_commute hcomm).symm
      rw [← add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero] at h2
      exact h2
    calc Φ t = Φ t * (NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A)) := by
          rw [h1, mul_one]
      _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hP t, one_mul]
  refine ⟨A, ?_, fun t w => ?_⟩
  · rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
    let T : Matrix (l ⊕ l) (l ⊕ l) ℝ →L[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ :=
      LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (l ⊕ l) (l ⊕ l) ℝ ℝ).toLinearMap
    have hT : HasDerivAt (fun t => (Φ t)ᵀ) (T (Φ 0 * A)) 0 := T.hasFDerivAt.comp_hasDerivAt 0 (hΦd 0)
    have hF := (hT.mul_const (Matrix.J l ℝ)).mul (hΦd 0)
    have hF0 : HasDerivAt (fun t => (Φ t)ᵀ * Matrix.J l ℝ * Φ t) 0 0 := by
      have e : (fun t => (Φ t)ᵀ * Matrix.J l ℝ * Φ t) = fun _ => Matrix.J l ℝ := funext hinv
      rw [e]
      exact hasDerivAt_const 0 _
    have huniq := hF.unique hF0
    simp only [T, hΦ0, one_mul, mul_one] at huniq
    have h2 : Aᵀ * Matrix.J l ℝ + Matrix.J l ℝ * A = 0 := by simpa using huniq
    show Aᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -A
    rw [mul_neg]
    exact eq_neg_of_add_eq_zero_left h2
  · rw [hΦw, hΦe t]
end PositivityTheory.ThKR
