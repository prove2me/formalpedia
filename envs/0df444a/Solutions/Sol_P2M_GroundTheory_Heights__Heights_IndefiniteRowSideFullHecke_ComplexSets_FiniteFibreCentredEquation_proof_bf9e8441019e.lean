-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_proof_bf9e8441019e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:57:48.947797+00:00
-- url     : https://prove2.me/submissions/2bd557a8-45a6-41ec-89f1-5480d5d6666b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteFibreCentredEquation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_eval_580bd4626eae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_coeff_364200b5094e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_eval_expand_f70ba1572af3

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
open Topology Filter Polynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteFibreCentredEquation
theorem _root_.solution (hI : FiniteFibreGermIntegral.Statement)
    (hW : WeierstrassPreparation.Statement) : FiniteFibreCentredEquation.Statement := by
  intro σ _ S w d A hS hfib g hg
  obtain ⟨N, a, ha, hrel⟩ := hI σ S w d A hS hfib (fun z => g z - g w) (hg.sub analyticAt_const)
  set f : (Option (Fin d) → ℂ) → ℂ := fun x =>
    x none ^ N + ∑ j, a j (A w + fun i => x (some i)) * x none ^ (j : ℕ) with hf_def
  have hlast : AnalyticAt ℂ (fun x : Option (Fin d) → ℂ => x none) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin d) => ℂ) none).analyticAt 0
  have hfirst : AnalyticAt ℂ (fun x : Option (Fin d) → ℂ => A w + fun i => x (some i)) 0 :=
    analyticAt_const.add ((ContinuousLinearMap.pi fun i : Fin d =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin d) => ℂ) (some i)).analyticAt 0)
  have hfan : AnalyticAt ℂ f 0 := by
    refine (hlast.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp_of_eq hfirst (show A w + (0 : Fin d → ℂ) = A w from add_zero _)).mul (hlast.pow _)

  set p : ℂ[X] := X ^ N + ∑ j : Fin N, C (a j (A w)) * X ^ (j : ℕ) with hp_def
  have hpm : p.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hpe : (fun t => f (pointWithLast 0 t)) = fun t => p.eval t := by
    funext t
    have h0 : (fun i => pointWithLast (0 : Fin d → ℂ) t (some i)) = 0 := rfl
    simp only [hf_def, hp_def, h0, add_zero, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
    rfl
  have hne : analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 ≠ ⊤ := by
    rw [hpe]
    intro htop
    have hpan : AnalyticOnNhd ℂ (fun t => p.eval t) Set.univ := fun t _ =>
      (Polynomial.differentiable p).analyticAt t
    have hall : Set.EqOn (fun t => p.eval t) 0 Set.univ :=
      hpan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) (analyticOrderAt_eq_top.1 htop)
    exact hpm.ne_zero (Polynomial.funext fun t => by simpa using hall (Set.mem_univ t))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = k :=
    ⟨_, (Nat.cast_analyticOrderNatAt hne).symm⟩
  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hW (Fin d) k f hfan hk
  refine ⟨k, fun m y => (FiniteFibreCentredEquation.centredPoly (g w) fun j => c j (y - A w)).coeff m, fun m => ?_, fun T => ?_, ?_⟩
  · simp only [FiniteFibreCentredEquation.centredPoly_coeff]
    refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((hc j).comp_of_eq (f := fun y : Fin d → ℂ => y - A w) (analyticAt_id.sub analyticAt_const)
      (sub_self _)).mul analyticAt_const
  · rw [← FiniteFibreCentredEquation.centredPoly_eval_expand, FiniteFibreCentredEquation.centredPoly_eval]
    simp [hc0]
  ·
    set φ : (σ → ℂ) → (Option (Fin d) → ℂ) := fun z => pointWithLast (A z - A w) (g z - g w) with hφ_def
    have hφc : ContinuousAt φ w := by
      refine continuousAt_pi.2 fun o => ?_
      cases o with
      | none => exact hg.continuousAt.sub continuousAt_const
      | some i => exact ((continuous_apply i).comp A.continuous).continuousAt.sub continuousAt_const
    have hφw : φ w = 0 := by
      funext o; cases o <;> simp [hφ_def, pointWithLast]
    have hφt : Tendsto φ (𝓝 w) (𝓝 0) := hφw ▸ hφc.tendsto
    filter_upwards [hφt.eventually hfe, hφt.eventually (he.continuousAt.eventually_ne he0), hrel]
      with z h1 h2 h3 hzX
    have hf0 : f (φ z) = 0 := by
      show (g z - g w) ^ N + ∑ j, a j (A w + (A z - A w)) * (g z - g w) ^ (j : ℕ) = 0
      rw [add_sub_cancel]
      exact h3 hzX
    have hω : (g z - g w) ^ k + ∑ j, c j (A z - A w) * (g z - g w) ^ (j : ℕ) = 0 := by
      rw [hf0] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left h2
    rw [← FiniteFibreCentredEquation.centredPoly_eval_expand, FiniteFibreCentredEquation.centredPoly_eval]
    exact hω
end FiniteFibreCentredEquation
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
