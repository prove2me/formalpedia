-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_spec_933dc8cb6ebe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:35.133863+00:00
-- url     : https://prove2.me/submissions/78723d31-fafd-43b4-930d-c7277979b14b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
variable {J : Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι R)} {s g f m u₀ v₀ : MRing ι R} (e : K → ℕ)
    (h : u₀ * f - v₀ * g ∈ P) (j : BlowUpIdx ι) :
    u₀ * blowUpGens s g f m e j - g * blowUpCof s m e u₀ v₀ j ∈ P := by
  rcases j with _ | _ | i
  · simp only [blowUpGens, blowUpCof]
    rw [show u₀ * (s * g) - g * (u₀ * s) = 0 by ring]
    exact P.zero_mem
  · simp only [blowUpGens, blowUpCof]
    rw [show u₀ * (f * m) - g * (v₀ * m) = m * (u₀ * f - v₀ * g) by ring]
    exact P.mul_mem_left _ h
  · simp only [blowUpGens, blowUpCof]
    rw [show u₀ * (f * powMonomial e i) - g * (v₀ * powMonomial e i) =
      powMonomial e i * (u₀ * f - v₀ * g) by ring]
    exact P.mul_mem_left _ h
end GroundTheory.Heights₂.Heights.NumbersDVR
