-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_standardFlag_saturated_e86c126ee556
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:46.668855+00:00
-- url     : https://prove2.me/submissions/5dcba758-d7e3-439a-b7bf-49006a653e96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (i : Fin 3) :
    (HermitianBundle.standard K 2).Saturated (standardFlag K i) := by
  intro a x ha hx
  change Fin 2 → 𝓞 K at x
  fin_cases i
  · change x ∈ (⊥ : Submodule (𝓞 K) (Fin 2 → 𝓞 K))
    change a • x ∈ (⊥ : Submodule (𝓞 K) (Fin 2 → 𝓞 K)) at hx
    rw [Submodule.mem_bot] at hx ⊢
    exact (smul_eq_zero.mp hx).resolve_left ha
  · change x ∈ LinearMap.range (firstIncl K)
    change a • x ∈ LinearMap.range (firstIncl K) at hx
    obtain ⟨b, hb⟩ := hx
    have h1 : (a • x) 1 = 0 := by rw [← hb]; simp
    rw [Pi.smul_apply, smul_eq_mul] at h1
    have hx1 : x 1 = 0 := (mul_eq_zero.mp h1).resolve_left ha
    refine ⟨x 0, funext fun i ↦ ?_⟩
    fin_cases i
    · simp
    · simp [hx1]
  · exact Submodule.mem_top
end GroundTheory.Heights₂.Heights
