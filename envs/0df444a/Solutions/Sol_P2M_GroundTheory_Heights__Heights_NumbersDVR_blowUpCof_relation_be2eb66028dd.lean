-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_relation_be2eb66028dd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:38.904272+00:00
-- url     : https://prove2.me/submissions/8f0df8d1-0911-4176-9336-94deb8016d54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_blowUpOf_of_sub_30a04624d21b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_spec_933dc8cb6ebe

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
theorem _root_.solution {P : Ideal (MRing ι R)} (hP : P.IsPrime) {s g f m u₀ v₀ : MRing ι R}
    (e : K → ℕ) (hg : g ∉ P) (h : u₀ * f - v₀ * g ∈ P) (j j' : BlowUpIdx ι) :
    newVar j * liftForm (blowUpCof s m e u₀ v₀ j') - newVar j' * liftForm (blowUpCof s m e u₀ v₀ j) ∈
      blowUpOf P (blowUpGens s g f m e) := by
  apply mem_blowUpOf_of_sub
  have h1 := blowUpCof_spec (s := s) (m := m) e h j
  have h2 := blowUpCof_spec (s := s) (m := m) e h j'
  generalize blowUpGens s g f m e j = x at h1 ⊢
  generalize blowUpGens s g f m e j' = x' at h2 ⊢
  generalize blowUpCof s m e u₀ v₀ j = a at h1 ⊢
  generalize blowUpCof s m e u₀ v₀ j' = a' at h2 ⊢
  have key : g * (x * a' - x' * a) ∈ P := by
    rw [show g * (x * a' - x' * a) = x' * (u₀ * x - g * a) - x * (u₀ * x' - g * a') by ring]
    exact P.sub_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)
  exact (hP.mem_or_mem key).resolve_left hg
end GroundTheory.Heights₂.Heights.NumbersDVR
