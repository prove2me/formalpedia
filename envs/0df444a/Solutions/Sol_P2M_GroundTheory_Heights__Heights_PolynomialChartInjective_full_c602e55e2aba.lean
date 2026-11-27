-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PolynomialChartInjective_full_c602e55e2aba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:50.398395+00:00
-- url     : https://prove2.me/submissions/60383c62-14ec-4411-af3a-0cc697ed693b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialChartInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCurveRegularPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialChartInjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalCurveRegularPoint_fderiv_eval_single_e2e36c26b6f3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PolynomialChartInjective
theorem _root_.solution : PolynomialChartInjective.Statement := by
  classical
  intro σ _ k t f w hk hlin
  set g : Fin (k + 1) → MvPolynomial σ ℂ := Fin.cons t f with hg
  set F : (σ → ℂ) → Fin (k + 1) → ℂ := fun z j ↦ eval z (g j) with hF
  set L : (σ → ℂ) →L[ℂ] (Fin (k + 1) → ℂ) :=
    ContinuousLinearMap.pi fun j ↦ fderiv ℂ (fun z : σ → ℂ ↦ eval z (g j)) w with hL
  have hFL : HasStrictFDerivAt F L w := hasStrictFDerivAt_pi.2 fun j ↦
    (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (g j) w trivial).hasStrictFDerivAt
  set r : Fin (k + 1) → σ → ℂ :=
    Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) with hr
  have hrow : ∀ j i, fderiv ℂ (fun z : σ → ℂ ↦ eval z (g j)) w (Pi.single i 1) = r j i := by
    intro j i
    rw [NormalCurveRegularPoint.fderiv_eval_single]
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [g, r]
  have hspan : Submodule.span ℂ (Set.range r) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank' (by simp [Module.finrank_fintype_fun_eq_card, hk])
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    let ψ : (σ → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun u ↦ ∑ i, u i * v i
        map_add' := fun a b ↦ by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun c a ↦ by simp [Finset.mul_sum, mul_assoc] }
    have hker : Submodule.span ℂ (Set.range r) ≤ LinearMap.ker ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h0 := congrFun hv j
      simp only [hL, ContinuousLinearMap.pi_apply, Pi.zero_apply] at h0
      rw [pi_eq_sum_univ' v, map_sum] at h0
      simp only [map_smul, smul_eq_mul, hrow] at h0
      simpa [ψ, mul_comm] using h0
    rw [hspan] at hker
    funext i
    have := hker (Submodule.mem_top (x := Pi.single i 1))
    simpa [ψ, Pi.single_apply] using this
  let e : (σ → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ) :=
    (LinearMap.linearEquivOfInjective L.toLinearMap hinj
      (by simp [Module.finrank_fintype_fun_eq_card, hk])).toContinuousLinearEquiv
  have hFe : HasStrictFDerivAt F (e : (σ → ℂ) →L[ℂ] (Fin (k + 1) → ℂ)) w := by
    convert hFL using 1
    ext v : 1
    rfl
  refine ⟨_, hFe.eventually_left_inverse, fun x hx y hy hxy ↦ ?_⟩
  have hFxy : F x = F y := by
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simpa [F, g] using hxy
    · simp only [F, g, Fin.cons_succ, hx.2 j, hy.2 j]
  rw [← hx.1, ← hy.1, hFxy]
end PolynomialChartInjective
end GroundTheory.Heights₂.Heights
