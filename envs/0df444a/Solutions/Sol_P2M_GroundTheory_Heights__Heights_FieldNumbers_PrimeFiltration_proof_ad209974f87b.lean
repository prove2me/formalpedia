-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_proof_ad209974f87b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:10.750806+00:00
-- url     : https://prove2.me/submissions/bb897802-51e8-4bdc-880b-a0b9cee9b11f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_relDim_cases_459ef14bf8c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_filtration_e7e80f1f0240

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution (h1 : HilbExactDivide.Statement.{u}) : PrimeFiltration.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  obtain ⟨r, Q, c, hQ, hhilb, hcount⟩ := filtration h1 I hI
  refine ⟨r, Q, c, hQ, Filter.Eventually.of_forall hhilb, ?_, ?_⟩
  · intro W hW _ _
    rw [← hcount W hW, Finset.card_filter]
  · intro j
    have := (hQ j).1
    rcases relDim_cases (hQ j).2.2 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
