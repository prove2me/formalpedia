-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_mem_d13b7ad741bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:17.137099+00:00
-- url     : https://prove2.me/submissions/610e885b-8c79-4fe6-b31e-123e88c8cfc1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_1fa83b0aeb12
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_of_ne_5d5baf016181

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance 2000] lexDecEq
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) {f : MRing ι F}
    (hf : f ∈ I) (m : Lex (Fin (Fintype.card K) → ℕ)) :
    weightedHomogeneousComponent (lexWeight (ι := ι)) m f ∈ I := by
  by_cases h : ∃ b, lexEmb K b = m
  · obtain ⟨b, rfl⟩ := h
    rw [component_lex]
    exact hI f hf b
  · push Not at h
    rw [component_lex_of_ne f m h]
    exact I.zero_mem
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
