-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.aprb_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:47:25.458809+00:00
-- url     : https://prove2.me/submissions/920d4628-371e-4d6e-982b-1294b56a5ff6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n d : ℕ} (Lm : V n →L[ℂ] V d) (hs : Function.Surjective Lm) :
    ∃ A : V n ≃L[ℂ] V d × V (n - d), ∀ v, (A v).1 = Lm v := by
  classical
  let K := LinearMap.ker (Lm : V n →ₗ[ℂ] V d)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl K
  let P : V n →ₗ[ℂ] K := Submodule.linearProjOfIsCompl K C hC
  have hrank : Module.finrank ℂ (V d) + Module.finrank ℂ K = Module.finrank ℂ (V n) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Lm : V n →ₗ[ℂ] V d)
    rwa [LinearMap.range_eq_top.mpr hs, finrank_top] at h1
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hrank
  have hK : Module.finrank ℂ K = n - d := by omega
  let eK : K ≃ₗ[ℂ] V (n - d) := LinearEquiv.ofFinrankEq K (V (n - d)) (by rw [hK]; simp)
  let T : V n →ₗ[ℂ] V d × V (n - d) := LinearMap.prod (Lm : V n →ₗ[ℂ] V d) (eK.toLinearMap ∘ₗ P)
  have hT : Function.Injective T := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun v hv => ?_)
    have h1 : Lm v = 0 := by simpa [T] using congrArg Prod.fst hv
    have h2 : P v = 0 := by simpa [T] using congrArg Prod.snd hv
    have hvK : v ∈ K := by simpa [K] using h1
    have h3 := Submodule.linearProjOfIsCompl_apply_left hC ⟨v, hvK⟩
    have h4 : (⟨v, hvK⟩ : K) = 0 := h3.symm.trans h2
    simpa using congrArg Subtype.val h4
  have hdim : Module.finrank ℂ (V n) = Module.finrank ℂ (V d × V (n - d)) := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    omega
  refine ⟨(LinearMap.linearEquivOfInjective T hT hdim).toContinuousLinearEquiv, fun v => ?_⟩
  rfl
end ReciprocityTheory.L2DbarEstimates.Y
