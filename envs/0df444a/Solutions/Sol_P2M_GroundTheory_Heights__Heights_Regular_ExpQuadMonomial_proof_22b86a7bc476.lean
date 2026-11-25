-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuadMonomial_proof_22b86a7bc476
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:38:52.597342+00:00
-- url     : https://prove2.me/submissions/0ec86d11-6808-4291-9a41-9d4db3d64991

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_eq_of_continuousAt_e738391b5387
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_cusp_ne_10e65f158bd3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_phi_analytic_cb4cbe93b925
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_phi_periodic_fdce41a51a71
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_exp_quad_ea718ee17e90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_mem_ball_of_forall_d3fc66dee939
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_castLE_214aca7e295d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_expCover_mem_bb0f4093b319
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_order_00de2034edca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_slice_noncusp_f59f6f6ffc67

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open ExpQuad
namespace GroundTheory.Heights₂.Heights.Regular
namespace ExpQuadMonomial
theorem _root_.solution (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    ExpQuadMonomial.Statement := by
  intro n a g P v
  classical
  obtain ⟨hΨ, hdesc⟩ := hD n a P.a_le (phi P v) (phi_analytic P v) (phi_periodic P v)
  have hΨ' : AnalyticOnNhd ℂ (psi P v) (puncturedChart P.a_le (ball 0 1)) := hΨ
  have hk : ∀ i, 0 ≤ intQuad (P.B i) v := fun i =>
    (slice_order P v hD hO (z := fun _ => (1 / 2 : ℂ))
      (mem_ball_of_forall fun _ => by norm_num) i (fun _ _ => by norm_num)).1
  have hsl : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ m : Fin n, (∀ j, j ≠ m → z j ≠ 0) → m.val < a →
      ∃ c : ℂ, c ≠ 0 ∧
        Tendsto (fun x => Complex.exp (psi P v (Function.update z m x))) (𝓝[≠] 0) (𝓝 c) := by
    intro z hz m hne hm
    have hmi : Fin.castLE P.a_le (⟨m.val, hm⟩ : Fin a) = m := Fin.ext rfl
    have := (slice_order P v hD hO hz ⟨m.val, hm⟩
      (fun j hj => hne _ (by rw [← hmi]; exact cusp_ne P hj))).2
    rwa [hmi] at this
  let G : (Fin n → ℂ) → ℂ := fun z => Complex.exp (psi P v z)
  let H : (Fin n → ℂ) → ℂ := fun z => Complex.exp (-psi P v z)
  have hGa : AnalyticOnNhd ℂ G (puncturedChart P.a_le (ball 0 1)) := fun z hz => (hΨ' z hz).cexp
  have hHa : AnalyticOnNhd ℂ H (puncturedChart P.a_le (ball 0 1)) :=
    fun z hz => (hΨ' z hz).neg.cexp
  have hWsub : ∀ z ∈ ball (0 : Fin n → ℂ) 1 ∩ {z | ∀ i, z i ≠ 0},
      z ∈ puncturedChart P.a_le (ball 0 1) :=
    fun z hz => ⟨hz.1, fun j => hz.2 _⟩
  obtain ⟨G', hG'a, hG'eq⟩ := hE n G
    (fun z hz => (hGa z (hWsub z hz)).differentiableAt.differentiableWithinAt)
    (fun z hz m hne => by
      by_cases hm : m.val < a
      · obtain ⟨c, -, hc⟩ := hsl z hz m hne hm
        exact ⟨c, hc⟩
      · exact slice_noncusp P hGa hz m hm hne)
  obtain ⟨H', hH'a, hH'eq⟩ := hE n H
    (fun z hz => (hHa z (hWsub z hz)).differentiableAt.differentiableWithinAt)
    (fun z hz m hne => by
      by_cases hm : m.val < a
      · obtain ⟨c, hc0, hc⟩ := hsl z hz m hne hm
        refine ⟨c⁻¹, ?_⟩
        simpa [H, Complex.exp_neg] using hc.inv₀ hc0
      · exact slice_noncusp P hHa hz m hm hne)
  refine ⟨hk, G', hG'a, fun z hz => ?_, fun w hw => ?_⟩
  · have h1 : G' z * H' z = 1 := eq_of_continuousAt (F₁ := fun y => G' y * H' y) (F₂ := fun _ => 1) hz
      ((hG'a z hz).continuousAt.mul (hH'a z hz).continuousAt) continuousAt_const
      (fun y hy hyW => by
        simp only [hG'eq y hy hyW, hH'eq y hy hyW, G, H, ← Complex.exp_add, add_neg_cancel,
          Complex.exp_zero])
    exact left_ne_zero_of_mul_eq_one h1
  · have hy := expCover_mem P hw
    have h1 : G' (expCover a w) = G (expCover a w) :=
      eq_of_continuousAt hy.1 (hG'a _ hy.1).continuousAt (hGa _ hy).continuousAt hG'eq
    have h2 : G (expCover a w) = Complex.exp (phi P v w) := by
      simp only [G, psi]
      rw [hdesc w hw]
    change Complex.exp (2 * Real.pi * Complex.I * qf (P.τ w) v) = _
    rw [exp_quad P v w, h1, h2, mul_comm]
    congr 1
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [expCover_castLE P, ← Complex.exp_nat_mul, mul_comm]
    congr 2
    exact_mod_cast (Int.toNat_of_nonneg (hk i)).symm
end ExpQuadMonomial
end GroundTheory.Heights₂.Heights.Regular
