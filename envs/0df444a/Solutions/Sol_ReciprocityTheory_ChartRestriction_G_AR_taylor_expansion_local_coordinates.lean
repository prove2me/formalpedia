-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_local_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:28:40.637494+00:00
-- url     : https://prove2.me/submissions/b53bbd27-b949-4951-b002-25e93bebf162

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_taylor_expansion_at_origin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR
open Filter Topology Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR
theorem _root_.solution {n a : ℕ} (g : V n → ℂ) (ζ : V n → V n) (U : Set (V n)) (x : V n)
    (hU : IsOpen U) (hx : x ∈ U) (hg : DifferentiableOn ℂ g U) (hζ : DifferentiableOn ℂ ζ U)
    (hζ0 : ζ x = 0) (hdet : (fderiv ℂ ζ x).det ≠ 0) (hO : g =O[𝓝 x] fun v => ‖v - x‖ ^ a) :
    ∃ b : (Fin n → ℕ) → ℂ,
      (fun v => g v - ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, ζ v k ^ α k)
        =O[𝓝 x] fun v => ‖v - x‖ ^ (a + 1) := by
  have hcζ : ContDiffOn ℂ ∞ ζ U := contDiffOn_euclidean.2 fun k =>
    contDiffOn_of_differentiableOn n _ U hU (differentiableOn_euclidean.1 hζ k)
  have hCA : ContDiffAt ℂ 1 ζ x := (hcζ.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_top)
  let E : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ ζ x : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hE : (E : V n →L[ℂ] V n) = fderiv ℂ ζ x := ContinuousLinearMap.ext fun _ => rfl
  have hf' : HasFDerivAt ζ (E : V n →L[ℂ] V n) x := by
    rw [hE]; exact (hζ.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  set ψ := hCA.localInverse hf' one_ne_zero with hψ
  have hψ0 : ψ 0 = x := by rw [← hζ0]; exact hCA.localInverse_apply_image hf' one_ne_zero
  have hψC : ContDiffAt ℂ 1 ψ 0 := by rw [← hζ0]; exact hCA.to_localInverse hf' one_ne_zero
  have hleft : ∀ᶠ v in 𝓝 x, ψ (ζ v) = v := (hCA.hasStrictFDerivAt' hf' one_ne_zero).eventually_left_inverse
  have hψt : Tendsto ψ (𝓝 0) (𝓝 x) := by
    have := hψC.continuousAt.tendsto; rwa [hψ0] at this
  have hSn : {u | DifferentiableAt ℂ ψ u ∧ ψ u ∈ U} ∈ 𝓝 (0 : V n) :=
    ((hψC.eventually (by simp)).mono fun u hu => hu.differentiableAt one_ne_zero).and
      (hψt.eventually (hU.mem_nhds hx))
  set U' := interior {u | DifferentiableAt ℂ ψ u ∧ ψ u ∈ U}
  have hG : DifferentiableOn ℂ (g ∘ ψ) U' := fun u hu =>
    have hu' := interior_subset hu
    ((hg.differentiableAt (hU.mem_nhds hu'.2)).comp u hu'.1).differentiableWithinAt
  have hψd : HasFDerivAt ψ (fderiv ℂ ψ 0) 0 := (hψC.differentiableAt one_ne_zero).hasFDerivAt
  have hGO : (g ∘ ψ) =O[𝓝 0] fun u => ‖u‖ ^ a := by
    refine (hO.comp_tendsto hψt).trans ?_
    have h1 := hψd.isBigO_sub
    rw [hψ0] at h1
    simp only [sub_zero] at h1
    exact h1.norm_norm.pow a
  obtain ⟨b, hb⟩ := taylor_expansion_at_origin (g ∘ ψ) U' isOpen_interior (mem_interior_iff_mem_nhds.2 hSn) hG hGO
  refine ⟨b, ?_⟩
  have hζt : Tendsto ζ (𝓝 x) (𝓝 0) := by
    have := (hζ.differentiableAt (hU.mem_nhds hx)).continuousAt.tendsto; rwa [hζ0] at this
  have hζO : (fun v => ζ v) =O[𝓝 x] fun v => v - x := by
    have := (hζ.differentiableAt (hU.mem_nhds hx)).hasFDerivAt.isBigO_sub
    simpa [hζ0] using this
  refine ((hb.comp_tendsto hζt).congr' (hleft.mono fun v hv => ?_) EventuallyEq.rfl).trans ?_
  · simp [hv]
  · exact hζO.norm_norm.pow (a + 1)
end ReciprocityTheory.ChartRestriction.G.AR
