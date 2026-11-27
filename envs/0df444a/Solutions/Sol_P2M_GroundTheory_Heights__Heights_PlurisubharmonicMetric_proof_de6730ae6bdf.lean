-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlurisubharmonicMetric_proof_de6730ae6bdf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:30.687524+00:00
-- url     : https://prove2.me/submissions/f09e23e0-0838-4435-95cf-362425449d41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_AnalyticAtEvalConeComp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_analyticAt_evalCone_comp_5cc3e96f85a5

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PlurisubharmonicMetric
theorem _root_.solution (hPts : ConePoints.Statement) (hMet : ChartMetric.Statement) : PlurisubharmonicMetric.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG e γ u₀ hγ hev
  have hw₀ : γ u₀ ∈ D.extPoints := hev.self_of_nhds
  obtain ⟨hz₀, la₀, hla₀, hrel₀⟩ := (hPts ι n P D d g hg).2 _ hw₀

  choose c hc using fun k ↦ Function.ne_iff.mp (hz₀.1 k)
  have hm₀ : evalCone (D.basePart₂ (γ u₀)) (chartMonomial c d) ≠ 0 := by
    simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

  obtain ⟨j, hj⟩ := Function.ne_iff.mp (hw₀.1 none)
  have hj' : D.newPart (γ u₀) j ≠ 0 := hj
  have hg₀ : evalCone (D.basePart₂ (γ u₀)) (g c j) ≠ 0 := by
    intro h0
    apply hj'
    rw [hrel₀ c hm₀ j, h0, mul_zero, zero_div]

  have hco : ∀ (o : Option ι) (i : Fin (D.extSizes o + 1)), AnalyticAt ℂ (fun u ↦ γ u o i) u₀ :=
    fun o i ↦ ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D.extSizes o + 1) ↦ ℂ) i).analyticAt _).comp
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun o ↦ Fin (D.extSizes o + 1) → ℂ) o).analyticAt _).comp hγ)
  have hold : ∀ f, AnalyticAt ℂ (fun u ↦ evalCone (D.basePart₂ (γ u)) f) u₀ :=
    analyticAt_evalCone_comp (fun u ↦ D.basePart₂ (γ u)) u₀ fun k i ↦ hco (some k) i
  have hM := hold (chartMonomial c d)
  have hG' := hold (g c j)
  have hnew : AnalyticAt ℂ (fun u ↦ D.newPart (γ u) j) u₀ := hco none j
  refine ⟨fun u ↦ D.newPart (γ u) j * evalCone (D.basePart₂ (γ u)) (chartMonomial c d) /
      evalCone (D.basePart₂ (γ u)) (g c j), (hnew.mul hM).div hG' hg₀, ?_, ?_⟩
  · simp only
    rw [hrel₀ c hm₀ j]
    field_simp
    exact hla₀
  · filter_upwards [hev, hM.continuousAt.eventually_ne hm₀, hG'.continuousAt.eventually_ne hg₀]
      with u hu hmu hgu
    obtain ⟨_, la, _, hrel⟩ := (hPts ι n P D d g hg).2 _ hu
    have hla : D.newPart (γ u) j * evalCone (D.basePart₂ (γ u)) (chartMonomial c d) /
        evalCone (D.basePart₂ (γ u)) (g c j) = la := by
      rw [hrel c hmu j]
      field_simp
    rw [hla]
    exact (hMet ι n P D N hN d g hg r G δ hG).2 _ hu c la hmu (hrel c hmu)
end PlurisubharmonicMetric
end GroundTheory.Heights₂.Heights
