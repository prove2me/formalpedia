-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumRatSection_proof_1f2dabfb1efd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:00.785948+00:00
-- url     : https://prove2.me/submissions/efec0410-91cf-448a-bcb4-72b9b9742917

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_eq_of_ringKrullDim_e3c92081b9b8

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
open GroundTheory.Heights₂.Heights.FieldNumbers
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace IntNumRatSection
theorem _root_.solution (h : CutRational.Statement.{u}) : IntNumRatSection.Statement.{u} := by
  intro F _ K _ _ ι _ n V hV hdim L A f g α β hf hg hfV hgV hA
  have hrel : relDim V = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    relDim_eq_of_ringKrullDim V (n + 1) hdim
  have hAeq : (fun k => (α k : ℤ) - β k) = A := funext hA
  have := h F K ι V hV n hrel α β f g hf hg hfV hgV L
  rw [hAeq] at this
  exact this
end IntNumRatSection
end GroundTheory.Heights₂.Heights.NumbersDVR
