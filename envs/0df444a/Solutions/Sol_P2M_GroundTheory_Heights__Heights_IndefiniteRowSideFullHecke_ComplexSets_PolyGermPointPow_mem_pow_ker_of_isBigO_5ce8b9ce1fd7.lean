-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_mem_pow_ker_of_isBigO_5ce8b9ce1fd7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:10.274683+00:00
-- url     : https://prove2.me/submissions/2380d1ba-f02b-4a85-bf60-ef929e219d11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyGermPointPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_coeff_eq_zero_of_isBigO_a896a5b521ef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_eval_smul_of_isHomogeneous_6fafba61571e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_ker_eval_eq_span_c590d7c396ab
import Theorems.Thm_UpperTheory_Reformulated_B_HomogeneousEvalSmul_eval_smul_of_isHomogeneous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter Asymptotics
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow
variable {σ : Type} [Fintype σ] (w : σ → ℂ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow
theorem _root_.solution {k : ℕ} {q : MvPolynomial σ ℂ}
    (hq : (fun z => eval z q) =O[𝓝 w] fun z => ‖z - w‖ ^ k) :
    q ∈ RingHom.ker (MvPolynomial.eval w) ^ k := by
  set q' := bind₁ (fun i => X i + C (w i)) q with hq'def
  have hev : ∀ y, eval y q' = eval (y + w) q := by
    intro y
    rw [hq'def, show (eval y : MvPolynomial σ ℂ →+* ℂ) = eval₂Hom (RingHom.id ℂ) y from rfl, eval₂Hom_bind₁]
    have hfun : (fun i => eval₂Hom (RingHom.id ℂ) y (X i + C (w i))) = y + w := by
      ext i
      simp only [map_add, eval₂Hom_X', eval₂Hom_C, RingHom.id_apply, Pi.add_apply]
    rw [hfun]
    rfl

  have hcomp : ∀ d < k, homogeneousComponent d q' = 0 := by
    intro d hd
    by_cases hdT : d ∈ Finset.range (q'.totalDegree + 1)
    swap
    · exact homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hdT)
    refine MvPolynomial.funext fun v => ?_
    let P : Polynomial ℂ := ∑ e ∈ Finset.range (q'.totalDegree + 1),
      Polynomial.monomial e (eval v (homogeneousComponent e q'))
    have hP : ∀ t, P.eval t = eval (t • v + w) q := by
      intro t
      rw [← hev]
      conv_rhs => rw [← sum_homogeneousComponent q']
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial, map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e q'), mul_comm]
    have hT : Tendsto (fun t : ℂ => t • v + w) (𝓝 0) (𝓝 w) := by
      simpa using ((continuous_id.smul continuous_const).add continuous_const).tendsto (0 : ℂ)
        (f := fun t : ℂ => t • v + w)
    have hPO : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k := by
      simp_rw [hP]
      refine (hq.comp_tendsto hT).trans (IsBigO.of_bound (‖v‖ ^ k) (Eventually.of_forall fun t => ?_))
      simp [norm_smul, mul_pow, mul_comm]
    have hc := coeff_eq_zero_of_isBigO hPO d hd
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', if_pos hdT] at hc
    simpa using hc
  have hmem : q' ∈ idealOfVars σ ℂ ^ k := by
    refine (mem_pow_idealOfVars_iff' k q').mpr fun x hx => ?_
    have := congrArg (coeff x) (hcomp _ hx)
    rwa [coeff_homogeneousComponent, if_pos rfl, coeff_zero] at this
  have hback : bind₁ (fun i => X i - C (w i)) q' = q := by
    rw [hq'def, bind₁_bind₁]
    simp [bind₁_X_right]
  have := Ideal.mem_map_of_mem (bind₁ (fun i => (X i - C (w i) : MvPolynomial σ ℂ))) hmem
  rw [Ideal.map_pow, idealOfVars, Ideal.map_span, ← Set.range_comp, hback] at this
  rw [GroundTheory.Heights₂.Heights.GradientAtPoint.ker_eval_eq_span]
  simpa [Function.comp_def, bind₁_X_right] using this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow
