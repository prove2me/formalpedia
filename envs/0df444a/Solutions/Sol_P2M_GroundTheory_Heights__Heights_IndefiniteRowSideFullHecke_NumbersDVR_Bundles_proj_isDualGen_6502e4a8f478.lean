-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_proj_isDualGen_6502e4a8f478
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:45.644845+00:00
-- url     : https://prove2.me/submissions/cab8a1ca-4a2a-4f1c-b65a-b9288d4bae8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
variable (F : Type*) [Field F]
variable {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
theorem _root_.solution (x : (Σ k, ι k) → Ω) :
    IsDualGen F x (frameBundle F (mseg x) (Pi.basisFun Ω (Fin 2))) 0
      (fun j : Fin 2 => (LinearMap.proj j : (Fin 2 → Ω) →ₗ[Ω] Ω)) := by
  intro s _
  have hmon : chartMon x s 0 = 1 := by simp [chartMon]
  refine ⟨fun j e he => ⟨e j, by simpa using mem_frameLat.mp he j, by simp [hmon]⟩, fun ψ hψ => ?_⟩
  refine ⟨fun j => ψ (Pi.single j 1), fun j => hψ _ (mem_frameLat.mpr fun q => ?_), ?_⟩
  · simp only [Pi.basisFun_repr]
    by_cases h : q = j
    · subst h
      simp
    · simp [h]
  · apply LinearMap.pi_ext
    intro i t
    simp only [hmon, inv_one, mul_one, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [show (Pi.single i t : Fin 2 → Ω) = t • Pi.single i 1 by
      ext j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h], map_smul, smul_eq_mul]
    simp [mul_comm]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
