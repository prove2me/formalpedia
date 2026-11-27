-- Prove2me | solution 1 for ReciprocityTheory.PTheta.domainOpen_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:10.497798+00:00
-- url     : https://prove2.me/submissions/f815ddc1-1e35-4a01-80b8-c05aab478702

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_symPart_posDef_of_sphere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
open sphereQuadraticPositivity
namespace ReciprocityTheory.PTheta
theorem _root_.solution : DomainOpenStatement := by
  unfold DomainOpenStatement
  intro ι _
  classical
  let Mt : (ι → ι → ℂ) → Matrix ι ι ℝ :=
    fun t => (of t).map Complex.im + ((of t).map Complex.im)ᵀ
  have hc : Continuous Mt := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (Complex.continuous_im.comp ((continuous_apply j).comp (continuous_apply i))).add
      (Complex.continuous_im.comp ((continuous_apply i).comp (continuous_apply j)))
  have hF : Continuous (fun q : (ι → ι → ℂ) × (ι → ℝ) => q.2 ⬝ᵥ (Mt q.1 *ᵥ q.2)) := by
    fun_prop
  have hset : {t : ι → ι → ℂ | of t ∈ ThetaDomain ι} =
      {t | ∀ y ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < y ⬝ᵥ (Mt t *ᵥ y)} := by
    ext t
    constructor
    · intro ht y hy
      have ht' : (Mt t).PosDef := ht
      have hy0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      have h0 := (Matrix.posDef_iff_dotProduct_mulVec.mp ht').2 hy0
      simpa using h0
    · intro ht
      exact symPart_posDef_of_sphere ((of t).map Complex.im) ht
  rw [hset, isOpen_iff_mem_nhds]
  intro t0 ht0
  have hev : ∀ y ∈ Metric.sphere (0 : ι → ℝ) 1,
      ∀ᶠ q : (ι → ι → ℂ) × (ι → ℝ) in nhds (t0, y), 0 < q.2 ⬝ᵥ (Mt q.1 *ᵥ q.2) :=
    fun y hy => (hF.tendsto (t0, y)).eventually (lt_mem_nhds (ht0 y hy))
  exact (isCompact_sphere (0 : ι → ℝ) 1).eventually_forall_of_forall_eventually
    (P := fun t y => 0 < y ⬝ᵥ (Mt t *ᵥ y)) hev
end ReciprocityTheory.PTheta
